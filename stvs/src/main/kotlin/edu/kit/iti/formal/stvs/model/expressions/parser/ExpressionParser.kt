package edu.kit.iti.formal.stvs.model.expressions.parser

import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParserBaseVisitor
import edu.kit.iti.formal.stvs.model.expressions.*
import org.antlr.v4.runtime.*
import org.antlr.v4.runtime.tree.ParseTree

/**
 * This class parses Expressions using the ANTLR parser generator library. The resulting Expression
 * format is an [Expression].
 *
 * @author Philipp
 */
class ExpressionParser : TestTableLanguageParserBaseVisitor<Expression> {
    private var columnName: String?
    private var columnAsVariable: Expression
    private var enumValues: Map<String, ValueEnum>

    /**
     * Creates an Expression parser without a type context. That means this parser can't parse enums.
     *
     * @param columnName name of this column's IoVariable for parsing single-sided expressions.
     */
    constructor(columnName: String?) {
        this.columnName = columnName
        this.columnAsVariable = VariableExpr(columnName)
        this.enumValues = HashMap() // empty enum value set, because no context given
    }

    /**
     * @param columnName name of this column's IoVariable for parsing single-sided expressions.
     * @param typeContext available types for figuring out whether an occuring string in an expression
     * is an enum-literal.
     */
    constructor(columnName: String?, typeContext: Collection<Type>) {
        this.columnName = columnName
        this.columnAsVariable = VariableExpr(columnName)
        this.enumValues = computeEnumValuesByName(typeContext)
    }

    private fun computeEnumValuesByName(typeSet: Collection<Type>): Map<String, ValueEnum> {
        val byName =
            typeSet.asSequence()
                .map { type -> this.filterEnumType(type) }
                .filterNotNull()
                .flatMap {
                    it.values.map { value -> value.valueString to value }
                }
                .toMap()
        return byName
    }

    private fun filterEnumType(type: Type): TypeEnum? {
        if (type is TypeEnum) {
            return type
        }
        return null
    }

    /**
     * @param expressionAsString the String to interpret as cell-expression
     * @return the expression covering the semantics of the given string interpreted as
     * cell-expression.
     * @throws ParseException When parsing could not be successful
     * @throws UnsupportedExpressionException When unsupported grammar features are reached
     */
    @Throws(ParseException::class, UnsupportedExpressionException::class)
    fun parseExpression(expressionAsString: String): Expression {
        val charStream = CharStreams.fromString(expressionAsString)
        val lexer = TestTableLanguageLexer(charStream)
        val tokens = CommonTokenStream(lexer)
        val parser = TestTableLanguageParser(tokens)
        parser.removeErrorListeners()
        parser.addErrorListener(ThrowingErrorListener())
        try {
            return this.visit(parser.cell())
        } catch (runtimeException: ParseRuntimeException) {
            throw runtimeException.parseException
        } catch (runtimeException: UnsupportedExpressionRuntimeException) {
            throw runtimeException.exception
        }
    }

    fun getColumnName(): String? {
        return columnName
    }

    fun setColumnName(columnName: String?) {
        this.columnName = columnName
        this.columnAsVariable = VariableExpr(columnName)
    }

    fun setTypeContext(context: Set<Type>) {
        this.enumValues = computeEnumValuesByName(context)
    }

    override fun visit(tree: ParseTree): Expression {
        return tree.accept(this)
    }

    override fun visitCell(ctx: TestTableLanguageParser.CellContext): Expression {
        val optionalExpression =
            ctx.chunk().stream().map { chunkContext: TestTableLanguageParser.ChunkContext -> chunkContext.accept(this) }
                .reduce { e1, e2 -> BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, e1, e2) }
        // We can always .get() this value, since the grammar enforces
        // that at least one chunk exists in a cell.
        return optionalExpression.get()
    }

    override fun visitDontcare(ctx: TestTableLanguageParser.DontcareContext): Expression {
        return LiteralExpr(ValueBool.TRUE)
    }

    override fun visitConstantTrue(ctx: TestTableLanguageParser.ConstantTrueContext?): Expression {
        return LiteralExpr(ValueBool.TRUE)
    }

    override fun visitConstantFalse(ctx: TestTableLanguageParser.ConstantFalseContext?): Expression {
        return LiteralExpr(ValueBool.TRUE)

    }

    override fun visitConstantString(ctx: TestTableLanguageParser.ConstantStringContext): Expression {
        return LiteralExpr(TODO())
    }

    override fun visitVariable(ctx: TestTableLanguageParser.VariableContext): Expression {
        // If we come here, its a top-level variable.
        // In this case there's an implicit equality with the column variable.
        val variableExpr = parseOccuringString(ctx)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.EQUALS, columnAsVariable, variableExpr)
    }

    override fun visitBvariable(ctx: TestTableLanguageParser.BvariableContext): Expression {
        return parseOccuringString(ctx.variable())
    }

    // A seemingly arbitrary string in a CellExpression can either be an Enum value or a variable...
    private fun parseOccuringString(ctx: TestTableLanguageParser.VariableContext): Expression {
        return parseArrayIndex(ctx).let { index: Int ->
            // If it has an index to it, like A[-2], its a variable for sure
            // (indices don't make sense for enums!)
            VariableExpr(parseIdentifier(ctx), index)
        } ?: maybeParseEnum(ctx)
    }

    private fun maybeParseEnum(ctx: TestTableLanguageParser.VariableContext): Expression {
        val identifier = parseIdentifier(ctx)
        val enumValue = enumValues[identifier]

        // If the enum value exists, we take it, else we think it's a variable.
        return if (enumValue == null) {
            VariableExpr(identifier)
        } else {
            LiteralExpr(enumValue)
        }
    }

    private fun parseArrayIndex(ctx: TestTableLanguageParser.VariableContext) =
        ctx.i().text.toInt().let { getArrayIndex(it) }

    private fun parseIdentifier(ctx: TestTableLanguageParser.VariableContext): String {
        return ctx.IDENTIFIER().text
    }

    override fun visitSinglesided(ctx: TestTableLanguageParser.SinglesidedContext): Expression {
        val op = binaryOperationFromToken(ctx.op.start)
        val rightSide = ctx.expr().accept(this)
        return BinaryFunctionExpr(op, columnAsVariable, rightSide)
    }

    private fun binaryOperationFromToken(token: Token): BinaryFunctionExpr.Op {
        return when (token.type) {
            TestTableLanguageLexer.EQUALS -> BinaryFunctionExpr.Op.EQUALS
            TestTableLanguageLexer.NOT_EQUALS -> BinaryFunctionExpr.Op.NOT_EQUALS
            TestTableLanguageLexer.GREATER_THAN -> BinaryFunctionExpr.Op.GREATER_THAN
            TestTableLanguageLexer.GREATER_EQUALS -> BinaryFunctionExpr.Op.GREATER_EQUALS
            TestTableLanguageLexer.LESS_THAN -> BinaryFunctionExpr.Op.LESS_THAN
            TestTableLanguageLexer.LESS_EQUALS -> BinaryFunctionExpr.Op.LESS_EQUALS
            TestTableLanguageLexer.AND -> BinaryFunctionExpr.Op.AND
            TestTableLanguageLexer.OR -> BinaryFunctionExpr.Op.OR
            TestTableLanguageLexer.XOR -> BinaryFunctionExpr.Op.XOR
            TestTableLanguageLexer.PLUS -> BinaryFunctionExpr.Op.PLUS
            TestTableLanguageLexer.MINUS -> BinaryFunctionExpr.Op.MINUS
            TestTableLanguageLexer.MULT -> BinaryFunctionExpr.Op.MULTIPLICATION
            TestTableLanguageLexer.DIV -> BinaryFunctionExpr.Op.DIVISION
            TestTableLanguageLexer.MOD -> BinaryFunctionExpr.Op.MODULO
            else -> throw ParseRuntimeException(
                ParseException(
                    token.line, token.charPositionInLine,
                    "Unsupported singlesided operation: \"" + token.type + "\""
                )
            )
        }
    }

    override fun visitPlus(ctx: TestTableLanguageParser.PlusContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.PLUS, left, right)
    }

    override fun visitSubstract(ctx: TestTableLanguageParser.SubstractContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.MINUS, left, right)
    }

    override fun visitMult(ctx: TestTableLanguageParser.MultContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.MULTIPLICATION, left, right)
    }

    override fun visitDiv(ctx: TestTableLanguageParser.DivContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.DIVISION, left, right)
    }

    override fun visitMod(ctx: TestTableLanguageParser.ModContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.MODULO, left, right)
    }

    override fun visitLogicalAnd(ctx: TestTableLanguageParser.LogicalAndContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, left, right)
    }

    override fun visitLogicalXor(ctx: TestTableLanguageParser.LogicalXorContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.XOR, left, right)
    }

    override fun visitLogicalOr(ctx: TestTableLanguageParser.LogicalOrContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.OR, left, right)
    }

    override fun visitInequality(ctx: TestTableLanguageParser.InequalityContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.NOT_EQUALS, left, right)
    }

    override fun visitEquality(ctx: TestTableLanguageParser.EqualityContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.EQUALS, left, right)
    }


    override fun visitCompare(ctx: TestTableLanguageParser.CompareContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(binaryOperationFromToken(ctx.op), left, right)
    }

    override fun visitInterval(ctx: TestTableLanguageParser.IntervalContext): Expression {
        val lower = ctx.lower.accept(this)
        val upper = ctx.upper.accept(this)
        return makeInterval(columnAsVariable, lower, upper)
    }

    // Transforms: variable "X", lower "-5", upper "1+2" into "x >= -5 && x <= 1+2" as expression
    private fun makeInterval(variable: Expression, lower: Expression, upper: Expression): Expression {
        val greaterThanLower: Expression =
            BinaryFunctionExpr(BinaryFunctionExpr.Op.GREATER_EQUALS, variable, lower)
        val smallerThanUpper: Expression =
            BinaryFunctionExpr(BinaryFunctionExpr.Op.LESS_EQUALS, variable, upper)

        return BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, greaterThanLower, smallerThanUpper)
    }

    override fun visitMinus(ctx: TestTableLanguageParser.MinusContext): Expression {
        val toBeNegated = ctx.sub.accept(this)
        return UnaryFunctionExpr(UnaryFunctionExpr.Op.UNARY_MINUS, toBeNegated)
    }

    override fun visitNegation(ctx: TestTableLanguageParser.NegationContext): Expression {
        return UnaryFunctionExpr(UnaryFunctionExpr.Op.NOT, ctx.sub.accept(this))
    }

    override fun visitParens(ctx: TestTableLanguageParser.ParensContext): Expression {
        return ctx.sub.accept(this)
    }

    override fun visitGuardedcommand(ctx: TestTableLanguageParser.GuardedcommandContext): Expression {
        throw UnsupportedExpressionRuntimeException("Guarded command (if)")
    }

    override fun visitFunctioncall(ctx: TestTableLanguageParser.FunctioncallContext): Expression {
        throw UnsupportedExpressionRuntimeException("Functioncall")
    }

    companion object {
        private fun getArrayIndex(index: Int): Int {
            if (index > 0) {
                throw UnsupportedExpressionRuntimeException("Positive Variable Index")
            }
            return index
        }
    }
}
