package edu.kit.iti.formal.stvs.model.expressions.parser

import edu.kit.iti.formal.stvs.model.expressions.*
import org.antlr.v4.runtime.*
import org.antlr.v4.runtime.tree.ParseTree
import org.antlr.v4.runtime.tree.TerminalNode

/**
 * This class parses Expressions using the ANTLR parser generator library. The resulting Expression
 * format is an [Expression].
 *
 * @author Philipp
 */
class ExpressionParser : CellExpressionBaseVisitor<Expression> {
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
    fun parseExpression(expressionAsString: String?): Expression {
        val charStream: CharStream = ANTLRInputStream(expressionAsString)
        val lexer = CellExpressionLexer(charStream)
        val tokens: TokenStream = CommonTokenStream(lexer)
        val parser = CellExpressionParser(tokens)
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

    override fun visitCell(ctx: CellExpressionParser.CellContext): Expression {
        val optionalExpression =
            ctx.chunk().stream().map { chunkContext: CellExpressionParser.ChunkContext -> chunkContext.accept(this) }
                .reduce { e1, e2 -> BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, e1, e2) }
        // We can always .get() this value, since the grammar enforces
        // that at least one chunk exists in a cell.
        return optionalExpression.get()
    }

    override fun visitDontcare(ctx: CellExpressionParser.DontcareContext): Expression {
        return LiteralExpr(ValueBool.TRUE)
    }

    override fun visitConstant(ctx: CellExpressionParser.ConstantContext): Expression {
        val literalExpr: Expression = LiteralExpr(valueFromConstantToken(ctx))
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.EQUALS, columnAsVariable, literalExpr)
    }

    override fun visitBconstant(ctx: CellExpressionParser.BconstantContext): Expression {
        return LiteralExpr(valueFromConstantToken(ctx.constant()))
    }

    override fun visitVariable(ctx: CellExpressionParser.VariableContext): Expression {
        // If we come here, its a top-level variable.
        // In this case there's an implicit equality with the column variable.
        val variableExpr = parseOccuringString(ctx)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.EQUALS, columnAsVariable, variableExpr)
    }

    override fun visitBvariable(ctx: CellExpressionParser.BvariableContext): Expression {
        return parseOccuringString(ctx.variable())
    }

    // A seemingly arbitrary string in a CellExpression can either be an Enum value or a variable...
    private fun parseOccuringString(ctx: CellExpressionParser.VariableContext): Expression {
        return parseArrayIndex(ctx)?.let { index: Int ->
            // If it has an index to it, like A[-2], its a variable for sure
            // (indices don't make sense for enums!)
            VariableExpr(parseIdentifier(ctx), index)
        } ?: maybeParseEnum(ctx)
    }

    private fun maybeParseEnum(ctx: CellExpressionParser.VariableContext): Expression {
        val identifier = parseIdentifier(ctx)
        val enumValue = enumValues[identifier]

        // If the enum value exists, we take it, else we think it's a variable.
        return if (enumValue == null) {
            VariableExpr(identifier)
        } else {
            LiteralExpr(enumValue)
        }
    }

    private fun parseArrayIndex(ctx: CellExpressionParser.VariableContext) =
        ctx.INTEGER()?.let { getArrayIndex(it) }

    private fun parseIdentifier(ctx: CellExpressionParser.VariableContext): String {
        return ctx.IDENTIFIER().text
    }

    private fun valueFromConstantToken(ctx: CellExpressionParser.ConstantContext): Value {
        // I have to trust ANTLR to not have any other values here... :/
        when (ctx.a.type) {
            CellExpressionLexer.INTEGER -> {
                val tooLongExpression = ParseException(
                    ctx.a.line,
                    ctx.a.charPositionInLine, "Integer value is too big: " + ctx.a.text
                )
                try {
                    val parsedInt = ctx.text.toShort().toInt()
                    return ValueInt(parsedInt)
                } catch (nfe: NumberFormatException) {
                    throw ParseRuntimeException(tooLongExpression)
                }
                return ValueBool.TRUE
            }

            CellExpressionLexer.T -> return ValueBool.TRUE
            CellExpressionLexer.F -> return ValueBool.FALSE
            else -> throw IllegalStateException("Can not parse given value.")
        }
    }

    override fun visitSinglesided(ctx: CellExpressionParser.SinglesidedContext): Expression {
        val op = binaryOperationFromToken(ctx.op.relOp)
        val rightSide = ctx.expr().accept(this)
        return BinaryFunctionExpr(op, columnAsVariable, rightSide)
    }

    private fun binaryOperationFromToken(token: Token): BinaryFunctionExpr.Op {
        return when (token.type) {
            CellExpressionLexer.EQUALS -> BinaryFunctionExpr.Op.EQUALS
            CellExpressionLexer.NOT_EQUALS -> BinaryFunctionExpr.Op.NOT_EQUALS
            CellExpressionLexer.GREATER_THAN -> BinaryFunctionExpr.Op.GREATER_THAN
            CellExpressionLexer.GREATER_EQUALS -> BinaryFunctionExpr.Op.GREATER_EQUALS
            CellExpressionLexer.LESS_THAN -> BinaryFunctionExpr.Op.LESS_THAN
            CellExpressionLexer.LESS_EQUALS -> BinaryFunctionExpr.Op.LESS_EQUALS
            CellExpressionLexer.AND -> BinaryFunctionExpr.Op.AND
            CellExpressionLexer.OR -> BinaryFunctionExpr.Op.OR
            CellExpressionLexer.XOR -> BinaryFunctionExpr.Op.XOR
            CellExpressionLexer.PLUS -> BinaryFunctionExpr.Op.PLUS
            CellExpressionLexer.MINUS -> BinaryFunctionExpr.Op.MINUS
            CellExpressionLexer.MULT -> BinaryFunctionExpr.Op.MULTIPLICATION
            CellExpressionLexer.DIV -> BinaryFunctionExpr.Op.DIVISION
            CellExpressionLexer.MOD -> BinaryFunctionExpr.Op.MODULO
            else -> throw ParseRuntimeException(
                ParseException(
                    token.line, token.charPositionInLine,
                    "Unsupported singlesided operation: \"" + token.type + "\""
                )
            )
        }
    }

    override fun visitPlus(ctx: CellExpressionParser.PlusContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.PLUS, left, right)
    }

    override fun visitSubstract(ctx: CellExpressionParser.SubstractContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.MINUS, left, right)
    }

    override fun visitMult(ctx: CellExpressionParser.MultContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.MULTIPLICATION, left, right)
    }

    override fun visitDiv(ctx: CellExpressionParser.DivContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.DIVISION, left, right)
    }

    override fun visitMod(ctx: CellExpressionParser.ModContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.MODULO, left, right)
    }

    override fun visitLogicalAnd(ctx: CellExpressionParser.LogicalAndContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, left, right)
    }

    override fun visitLogicalXor(ctx: CellExpressionParser.LogicalXorContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.XOR, left, right)
    }

    override fun visitLogicalOr(ctx: CellExpressionParser.LogicalOrContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.OR, left, right)
    }

    override fun visitInequality(ctx: CellExpressionParser.InequalityContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.NOT_EQUALS, left, right)
    }

    override fun visitEquality(ctx: CellExpressionParser.EqualityContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.EQUALS, left, right)
    }


    override fun visitCompare(ctx: CellExpressionParser.CompareContext): Expression {
        val left = ctx.left.accept(this)
        val right = ctx.right.accept(this)
        return BinaryFunctionExpr(binaryOperationFromToken(ctx.op), left, right)
    }

    override fun visitInterval(ctx: CellExpressionParser.IntervalContext): Expression {
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

    override fun visitMinus(ctx: CellExpressionParser.MinusContext): Expression {
        val toBeNegated = ctx.sub.accept(this)
        return UnaryFunctionExpr(UnaryFunctionExpr.Op.UNARY_MINUS, toBeNegated)
    }

    override fun visitNegation(ctx: CellExpressionParser.NegationContext): Expression {
        return UnaryFunctionExpr(UnaryFunctionExpr.Op.NOT, ctx.sub.accept(this))
    }

    override fun visitParens(ctx: CellExpressionParser.ParensContext): Expression {
        return ctx.sub.accept(this)
    }

    override fun visitGuardedcommand(ctx: CellExpressionParser.GuardedcommandContext): Expression {
        throw UnsupportedExpressionRuntimeException("Guarded command (if)")
    }

    override fun visitFunctioncall(ctx: CellExpressionParser.FunctioncallContext): Expression {
        throw UnsupportedExpressionRuntimeException("Functioncall")
    }

    companion object {
        private fun getArrayIndex(node: TerminalNode): Int {
            val index = node.text.toInt()
            if (index > 0) {
                throw UnsupportedExpressionRuntimeException("Positive Variable Index")
            }
            return index
        }
    }
}
