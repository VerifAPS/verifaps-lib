package edu.kit.iti.formal.stvs.model.code

import edu.kit.iti.formal.automation.IEC61131Facade.file
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.VariableCategory
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import org.antlr.v4.runtime.ANTLRInputStream
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Token
import java.util.*
import java.util.function.Consumer
import java.util.stream.Collectors

/**
 * Represents the formal model of source code (extracted from [Code]).
 * @author Lukas Fritsch
 */
class ParsedCode
/**
 * Creates a parsed code.
 *
 * @param foldableCodeBlocks list of codeblocks
 * @param definedVariables list of all defined variables (in the source code)
 * @param definedTypes list of all defined types (in the source code)
 */(
    val foldableCodeBlocks: List<FoldableCodeBlock>,
    val definedVariables: List<CodeIoVariable>, @JvmField val definedTypes: List<Type>
) {
    /**
     * A visitor for type declarations. Builds a list of types which have been declared in the code.
     */
    private class TypeDeclarationVisitor : DefaultVisitor<Void?>() {
        private val definedTypes: MutableList<Type> = ArrayList()

        init {
            definedTypes.add(TypeBool.BOOL)
            definedTypes.add(TypeInt.INT)
        }

        override fun visit(decls: TypeDeclarations): Void? {
            decls.forEach { it.accept(this) }
            return null
        }

        override fun visit(enumType: EnumerationTypeDeclaration): Void? {
            if (enumType.allowedValues.isNotEmpty()) {
                val type = TypeEnum(
                    enumType.name,
                    enumType.allowedValues.stream().map { obj: Token -> obj.text }.collect(Collectors.toList())
                )
                definedTypes.add(type)
            }
            return null
        }

        fun getDefinedTypes(): List<Type> {
            return definedTypes
        }
    }

    /**
     * A visitor which visits a [ProgramDeclaration] and builds a list of i/o variables
     * defined therein.
     */
    private class VariableVisitor : DefaultVisitor<Void?>() {
        private val definedVariables: MutableList<CodeIoVariable> = ArrayList()

        override fun visit(program: ProgramDeclaration): Void? {
            program.scope.variables.forEach(Consumer { variableEntry: VariableDeclaration ->
                // String varName = variableEntry.getKey();
                val category = getCategoryFromDeclaration(variableEntry)
                val dataTypeName = Optional.ofNullable(
                    variableEntry.dataType!!.name
                )
                if (category.isPresent && dataTypeName.isPresent) {
                    definedVariables
                        .add(CodeIoVariable(category.get(), dataTypeName.get(), variableEntry.name))
                }
            })
            return null
        }

        private fun getCategoryFromDeclaration(varDecl: VariableDeclaration): Optional<VariableCategory> {
            if (varDecl.isConstant) {
                return Optional.empty()
            }
            if (varDecl.isInput) return Optional.of(VariableCategory.INPUT)
            if (varDecl.isOutput) return Optional.of(VariableCategory.OUTPUT)
            if (varDecl.isLocal) return Optional.of(VariableCategory.LOCAL)
            if (varDecl.isInternal) return Optional.of(VariableCategory.LOCAL)
            if (varDecl.isInOut) return Optional.of(VariableCategory.INOUT)
            return Optional.empty()
        }

        fun getDefinedVariables(): List<CodeIoVariable> {
            return definedVariables
        }
    }

    /**
     * A visitor which visits [FunctionDeclaration]s and builds a list of
     * [FoldableCodeBlock]s, where each function declaration corresponds to one block.
     */
    private class BlockVisitor : DefaultVisitor<Void?>() {
        private val foldableCodeBlocks: MutableList<FoldableCodeBlock> = ArrayList()

        private fun addBlock(topElement: Top) {
            foldableCodeBlocks.add(
                FoldableCodeBlock(
                    topElement.ruleContext!!.start.line,
                    topElement.ruleContext!!.stop.line
                )
            )
        }

        override fun visit(function: FunctionDeclaration): Void? {
            addBlock(function)
            return null
        }

        override fun visit(program: ProgramDeclaration): Void? {
            addBlock(program)
            return null
        }

        fun getFoldableCodeBlocks(): List<FoldableCodeBlock> {
            return this.foldableCodeBlocks
        }
    }

    companion object {
        /**
         * Parses a code. The handlers and listeners provided as parameters are called with the results
         * of the parsing; i.e. the parsedCodeListener is called with the resulting [ParsedCode],
         * the parsedTokenHandler is called with the list of parsed tokens etc.
         *
         * @param input the source code to parse
         * @param parsedTokenHandler a handler for lexed tokens
         * @param syntaxErrorsListener listener for a list of [SyntaxError]s
         * @param parsedCodeListener listener for parsed code.
         */
        @JvmStatic
        fun parseCode(
            input: String?, parsedTokenHandler: ParsedTokenHandler?,
            syntaxErrorsListener: ParsedSyntaxErrorHandler, parsedCodeListener: ParsedCodeHandler
        ) {
            val syntaxErrorListener = SyntaxErrorListener()

            val stream = CharStreams.fromString(input) //, parsedTokenHandler, syntaxErrorListener);
            //TODO parsedTokenHandler?
            val ast = parse(stream, syntaxErrorListener)

            syntaxErrorsListener.accept(syntaxErrorListener.syntaxErrors)

            // Find types in parsed code
            val typeVisitor = TypeDeclarationVisitor()
            ast.accept(typeVisitor)
            val definedTypesByName: MutableMap<String, Type> = HashMap()
            typeVisitor.getDefinedTypes()
                .forEach(Consumer { type: Type -> definedTypesByName[type.typeName] = type })

            // Find IoVariables in parsed code
            val variableVisitor = VariableVisitor()
            ast.accept(variableVisitor)

            // Find code blocks in parsed code
            val blockVisitor = BlockVisitor()
            ast.accept(blockVisitor)
            val foldableCodeBlocks = blockVisitor.getFoldableCodeBlocks()

            parsedCodeListener.accept(
                ParsedCode(
                    foldableCodeBlocks,
                    variableVisitor.getDefinedVariables(), typeVisitor.getDefinedTypes()
                )
            )
        }

        /**
         * Parses a token stream.
         *
         * @param tokenStream         The token stream to parse
         * @param syntaxErrorListener The listener to invoke on syntax errors
         * @return The AST constructed from the token stream
         */
        private fun parse(tokenStream: CharStream, syntaxErrorListener: SyntaxErrorListener): PouElements {
            return file(tokenStream)
        }

        /**
         * Lex a given code.
         * @param input The code to lex
         * @param parsedTokenHandler Is called with the resulting list of tokens
         * @param syntaxErrorListener Is given to the lexer (and invoked on syntax errors)
         * @return The lexer used for lexing
         */
        private fun lex(
            input: String, parsedTokenHandler: ParsedTokenHandler,
            syntaxErrorListener: SyntaxErrorListener
        ): IEC61131Lexer {
            val lexer = IEC61131Lexer(ANTLRInputStream(input))
            lexer.removeErrorListeners()
            lexer.addErrorListener(syntaxErrorListener)
            parsedTokenHandler.accept(lexer.allTokens)
            lexer.reset()
            return lexer
        }
    }
}
