package edu.kit.iti.formal.stvs.model.code

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.IEC61131Facade.file
import edu.kit.iti.formal.automation.IEC61131Facade.fileResolve
import edu.kit.iti.formal.automation.datatypes.DataTypeVisitor
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.VariableCategory
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import org.antlr.v4.runtime.ANTLRInputStream
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams

/**
 * Represents the formal model of source code (extracted from [Code]).
 * @author Lukas Fritsch
 */
data class ParsedCode
/**
 * Creates a parsed code.
 *
 * @param foldableCodeBlocks list of codeblocks
 * @param definedVariables list of all defined variables (in the source code)
 * @param definedTypes list of all defined types (in the source code)
 */(
    val foldableCodeBlocks: List<FoldableCodeBlock> = listOf(),
    val definedVariables: List<CodeIoVariable> = listOf(),
    val definedTypes: List<Type> = listOf()
) {
    /**
     * A visitor for type declarations. Builds a list of types which have been declared in the code.
     */
    private class TypeDeclarationVisitor : AstVisitor<Unit>() {
        val definedTypes = arrayListOf<Type>()

        init {
            definedTypes.add(TypeBool.BOOL)
            definedTypes.add(TypeInt.INT)
        }

        override fun visit(typeDeclarations: TypeDeclarations) {
            typeDeclarations.forEach { it.accept(this) }
        }

        override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
            if (enumerationTypeDeclaration.allowedValues.isNotEmpty()) {
                val type = TypeEnum(
                    enumerationTypeDeclaration.name,
                    enumerationTypeDeclaration.allowedValues.map { it.text }
                )
                definedTypes.add(type)
            }
        }

        override fun defaultVisit(obj: Any) {}
    }

    /**
     * A visitor which visits a [ProgramDeclaration] and builds a list of i/o variables
     * defined therein.
     */
    private class VariableVisitor : AstVisitor<Unit>() {
        val definedVariables = arrayListOf<CodeIoVariable>()

        override fun visit(programDeclaration: ProgramDeclaration) {
            programDeclaration.scope.variables.forEach{
                // String varName = variableEntry.getKey();
                val category = getCategoryFromDeclaration(it)
                val dataTypeName = it.dataType?.name
                if (category != null && dataTypeName != null) {
                    definedVariables.add(CodeIoVariable(category, dataTypeName, it.name))
                }
            }
        }

        override fun defaultVisit(obj: Any) {}

        private fun getCategoryFromDeclaration(varDecl: VariableDeclaration): VariableCategory? {
            return when {
                varDecl.isConstant -> null
                varDecl.isInput -> VariableCategory.INPUT
                varDecl.isOutput -> VariableCategory.OUTPUT
                varDecl.isLocal -> VariableCategory.LOCAL
                varDecl.isInternal -> VariableCategory.LOCAL
                varDecl.isInOut -> VariableCategory.INOUT
                else -> null
            }
        }
    }

    /**
     * A visitor which visits [FunctionDeclaration]s and builds a list of
     * [FoldableCodeBlock]s, where each function declaration corresponds to one block.
     */
    private class BlockVisitor : AstVisitor<Unit>() {
        val foldableCodeBlocks = arrayListOf<FoldableCodeBlock>()

        private fun addBlock(topElement: Top) {
            foldableCodeBlocks.add(
                FoldableCodeBlock(
                    topElement.ruleContext!!.start.line,
                    topElement.ruleContext!!.stop.line
                )
            )
        }

        override fun visit(functionDeclaration: FunctionDeclaration) = addBlock(functionDeclaration)
        override fun defaultVisit(obj: Any) {}

        override fun visit(programDeclaration: ProgramDeclaration) = addBlock(programDeclaration)
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
            input: String, parsedTokenHandler: ParsedTokenHandler,
            syntaxErrorsListener: ParsedSyntaxErrorHandler, parsedCodeListener: ParsedCodeHandler
        ) {
            val syntaxErrorListener = SyntaxErrorListener()

            lex(input, parsedTokenHandler, syntaxErrorListener)

            val stream = CharStreams.fromString(input) //, parsedTokenHandler, syntaxErrorListener);

            try {
                val ast = parse(stream, syntaxErrorListener)
                syntaxErrorsListener.accept(syntaxErrorListener.syntaxErrors)

                // Find types in parsed code
                val typeVisitor = TypeDeclarationVisitor()
                ast.accept(typeVisitor)
                //val definedTypesByName = typeVisitor.definedTypes.associateBy { it.typeName }

                // Find IoVariables in parsed code
                val variableVisitor = VariableVisitor()
                ast.accept(variableVisitor)

                // Find code blocks in parsed code
                val blockVisitor = BlockVisitor()
                ast.accept(blockVisitor)
                val foldableCodeBlocks = blockVisitor.foldableCodeBlocks

                parsedCodeListener.accept(
                    ParsedCode(
                        foldableCodeBlocks,
                        variableVisitor.definedVariables,
                        typeVisitor.definedTypes
                    )
                )
            } catch (_: SyntaxErrorReporter.ParserException) {
                //ignore
            }
        }

        /**
         * Parses a token stream.
         *
         * @param tokenStream         The token stream to parse
         * @param syntaxErrorListener The listener to invoke on syntax errors
         * @return The AST constructed from the token stream
         */
        private fun parse(tokenStream: CharStream, syntaxErrorListener: SyntaxErrorListener): PouElements {
            val (pous, errors) =  fileResolve(tokenStream, true)
            return pous
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
