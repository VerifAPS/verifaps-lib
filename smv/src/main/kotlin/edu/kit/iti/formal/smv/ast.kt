package edu.kit.iti.formal.smv.ast

import edu.kit.iti.formal.smv.*
import edu.kit.iti.formal.util.HasMetadata
import edu.kit.iti.formal.util.HasMetadataImpl
import org.antlr.v4.runtime.Token
import java.math.BigDecimal
import java.math.BigInteger
import java.util.*
import kotlin.collections.ArrayList


/**
 *
 *
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
interface SOperator {
    fun symbol(): String
    fun precedence(): Int
}

/**
 *
 * @author Alexander Weigl
 * @version 1 (09.04.18)
 */
sealed class SMVAst : HasMetadata {
    fun repr(): String = SMVPrinter.toString(this)
    abstract fun <T> accept(visitor: SMVAstVisitor<T>): T
    abstract fun clone(): SMVAst

    private val metadata by lazy { HasMetadataImpl() }
    override fun <T> getMetadata(clazz: Class<T>): T? = metadata.getMetadata(clazz)
    override fun <T : Any> setMetadata(clazz: Class<T>, obj: T) = metadata.setMetadata(clazz, obj)
    override fun getAllMetadata(): Collection<Any> = metadata.getAllMetadata()
}

data class SAssignment(
        /**
         *
         */
        var target: SVariable,
        /**
         *
         */
        var expr: SMVExpr) : SMVAst() {
    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    override fun clone() = copy()
}

data class SBinaryExpression(private var _left: SMVExpr,
                             var operator: SBinaryOperator,
                             private var _right: SMVExpr)
    : SMVExpr() {

    var left: SMVExpr
        get() = _left
        set(value) {
            if (value === this) throw IllegalArgumentException()
            _left = value
        }

    var right: SMVExpr
        get() = _right
        set(value) {
            if (value === this) throw IllegalArgumentException()
            _right = value
        }


    override val dataType: SMVType?
        get() = SMVTypes.infer(operator, left.dataType!!, right.dataType!!)

    override fun inModule(module: String): SBinaryExpression {
        return SBinaryExpression(left.inModule(module),
                operator, right.inModule(module))
    }

    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    override fun clone() = SBinaryExpression(left.clone(), operator, right.clone())
}


/**
 *
 */
data class SCaseExpression(var cases: MutableList<Case> = arrayListOf()) : SMVExpr() {

    override val dataType: SMVType?
        get() {
            val list = cases.map { a: Case -> a.then.dataType!! }
            return SMVTypes.infer(list)
        }

    fun add(condition: SMVExpr, value: SMVExpr) {
        cases.add(Case(condition, value))
    }

    fun compress(): SMVExpr {
        // if all cases have the same value then finish
        if (cases.size == 0) return this
        val firstCase = cases[0]
        val b = cases.stream().allMatch { aCase -> firstCase.then == aCase.then }
        if (b)
            return firstCase.then
        //
        val esac = SCaseExpression()
        var previous = firstCase
        var condition = previous.condition

        for (i in 1 until cases.size) {
            val current = cases[i]
            if (previous.then == current.then) {
                condition = condition.or(current.condition)
            } else {
                esac.addCase(condition, previous.then)
                previous = current
                condition = current.condition
            }
        }
        esac.addCase(condition, previous.then)
        return esac
    }

    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    override fun inModule(module: String): SCaseExpression {
        val sCaseExpression = SCaseExpression()
        for (c in cases) {
            sCaseExpression.add(c.condition.inModule(module), c.then.inModule(module))
        }
        return sCaseExpression
    }

    fun addCase(cond: SMVExpr, `var`: SMVExpr): Case {
        val c = Case(cond, `var`)
        cases.add(c)
        return c
    }


    /**
     *
     */
    data class Case(
            /**
             *
             */
            var condition: SMVExpr,
            /**
             *
             */
            var then: SMVExpr
    ) {
        override fun toString(): String {
            return ":: $condition->$then"
        }

        fun clone(): Case = Case(condition.clone(), then.clone())
    }

    override fun clone() = SCaseExpression(cases.map { it.clone() }.toMutableList())

}


/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
data class SFunction(
        val name: String,
        var arguments: List<SMVExpr>) : SMVExpr() {
    var typeSolver: FunctionTypeSolver? = null

    override val dataType: SMVType?
        get() = typeSolver?.invoke(this)

    constructor(funcName: String, vararg expr: SMVExpr) :
            this(funcName, Arrays.asList(*expr))

    override fun clone() = SFunction(name, arguments.map { it.clone() })

    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    override fun inModule(module: String): SFunction {
        return SFunction(name,
                arguments.map { a -> a.inModule(module) })
    }
}

sealed class SLiteral(open val value: Any, override val dataType: SMVType) : SMVExpr() {
    override fun <T> accept(visitor: SMVAstVisitor<T>): T = visitor.visit(this)

    abstract override fun clone(): SLiteral

    companion object {
        @JvmStatic
        val TRUE = SBooleanLiteral(true)

        @JvmStatic
        val FALSE = SBooleanLiteral(false)

        @JvmStatic
        fun integer(from: Long) = integer(BigInteger.valueOf(from))

        @JvmStatic
        fun integer(from: BigInteger) = SIntegerLiteral(from)

        /*@JvmStatic
        fun create(value: Any) = LiteralBuilder(value)

        class LiteralBuilder(value: Any) {
            private val literal = SLiteral(value)

            fun with(width: Int, signed: Boolean) =
                    with(SMVWordType(signed, width))

            fun withSigned(width: Int) =
                    with(width, true)

            fun withUnsigned(width: Int) =
                    with(width, false)

            fun asBool() = with(SMVTypes.BOOLEAN)

            fun with(type: SMVType): SLiteral {
                literal.dataType = type
                return literal
            }
        }*/
    }
}

data class SIntegerLiteral(override var value: BigInteger)
    : SLiteral(value, SMVTypes.INT) {
    override fun inModule(module: String): SMVExpr = SIntegerLiteral(value)

    override fun clone() = copy()
}

data class SFloatLiteral(override var value: BigDecimal)
    : SLiteral(value, SMVTypes.FLOAT) {
    override fun inModule(module: String): SMVExpr = SFloatLiteral(value)
    override fun clone() = copy()
}

data class SWordLiteral(override var value: BigInteger,
                        override var dataType: SMVWordType)
    : SLiteral(value, dataType) {
    override fun inModule(module: String): SMVExpr = SWordLiteral(value, dataType)
    override fun clone() = copy()
}

data class SBooleanLiteral(override var value: Boolean)
    : SLiteral(value, SMVTypes.BOOLEAN) {
    override fun inModule(module: String): SMVExpr = SBooleanLiteral(value)
    override fun clone() = copy()
}

data class SEnumLiteral(override var value: String,
                        override var dataType: EnumType = SMVTypes.GENERIC_ENUM)
    : SLiteral(value, dataType) {
    override fun inModule(module: String): SMVExpr = SEnumLiteral(value)
    override fun clone() = copy()
}

// Use with caution!
data class SGenericLiteral(override var value: Any,
                           override var dataType: SMVType)
    : SLiteral(value, dataType) {
    override fun inModule(module: String): SMVExpr = SGenericLiteral(value, dataType)
    override fun clone() = copy()
}


abstract class SMVExpr : SMVAst() {
    abstract val dataType: SMVType?

    //region builder methods
    fun eventually(): SQuantified = SQuantified(STemporalOperator.F, this)

    fun globally(): SQuantified = SQuantified(STemporalOperator.G, this)

    operator fun next(): SQuantified = SQuantified(STemporalOperator.X, this)

    fun since(): SQuantified = SQuantified(STemporalOperator.S, this)

    fun once(): SQuantified = SQuantified(STemporalOperator.O, this)

    fun until(other: SMVExpr): SQuantified = SQuantified(STemporalOperator.U, this, other)

    infix fun equal(e: SMVExpr): SBinaryExpression = op(SBinaryOperator.EQUAL, e)

    infix fun and(e: SMVExpr): SBinaryExpression = op(SBinaryOperator.AND, e)

    infix fun or(e: SMVExpr): SBinaryExpression = op(SBinaryOperator.OR, e)

    fun op(o: SBinaryOperator, e: SMVExpr): SBinaryExpression {
        val product = SBinaryExpression(this, o, e)
        product.operator = o
        product.right = e
        return product
    }

    operator fun plus(e: SMVExpr) = op(SBinaryOperator.PLUS, e)
    operator fun div(e: SMVExpr) = op(SBinaryOperator.DIV, e)
    operator fun minus(e: SMVExpr) = op(SBinaryOperator.MINUS, e)
    operator fun times(e: SMVExpr) = op(SBinaryOperator.MUL, e)

    infix fun le(e: SMVExpr) = op(SBinaryOperator.LESS_EQUAL, e)
    infix fun lt(e: SMVExpr) = op(SBinaryOperator.LESS_THAN, e)
    infix fun ge(e: SMVExpr) = op(SBinaryOperator.GREATER_EQUAL, e)
    infix fun gt(e: SMVExpr) = op(SBinaryOperator.GREATER_THAN, e)
    infix fun eq(e: SMVExpr) = op(SBinaryOperator.EQUAL, e)
    infix fun neq(e: SMVExpr) = op(SBinaryOperator.NOT_EQUAL, e)


    operator fun not(): SUnaryExpression = SUnaryExpression(SUnaryOperator.NEGATE, this)

    fun negate(): SUnaryExpression = SUnaryExpression(SUnaryOperator.MINUS, this)

    infix fun implies(e: SMVExpr): SMVExpr = op(SBinaryOperator.IMPL, e)

    /**
     * prefiexed and expression
     */
    fun inModule(module: SVariable): SMVExpr {
        return inModule(module.name)
    }

    abstract fun inModule(module: String): SMVExpr

    fun wordConcat(b: SMVExpr): SMVExpr =
            op(SBinaryOperator.WORD_CONCAT, b)

    fun bitAccess(from: Long, to: Long) = SMVFacade.bitAccess(this, from, to)

    operator fun get(range: IntRange): SMVExpr {
        return bitAccess(range.start.toLong(), range.last.toLong())
    }

    fun inNext(): SFunction =
            SFunction("next", this)
    //endregion

    abstract override fun clone(): SMVExpr

    fun replaceExhaustive(definitions: Map<out SMVExpr, SMVExpr>): SMVExpr {
        val r = ExpressionReplacerRecur(definitions)
        return accept(r) as SMVExpr
    }
}


operator fun MutableList<SAssignment>.set(eq: SVariable, value: SMVExpr) {
    this.add(SAssignment(eq, value))
}

operator fun MutableList<SAssignment>.get(eq: SVariable): SMVExpr? {
    return this.find { it.target == eq }?.expr
}


data class SMVModule
@JvmOverloads constructor(
        var name: String,
        /**
         *
         */
        var inputVars: MutableList<SVariable> = ArrayList(),
        var moduleParameters: MutableList<SVariable> = ArrayList(),
        /**
         *
         */
        var stateVars: MutableList<SVariable> = ArrayList(),
        /**
         *
         */
        var frozenVars: MutableList<SVariable> = ArrayList(),
        var initAssignments: MutableList<SAssignment> = ArrayList(),
        var invariants: MutableList<SMVExpr> = ArrayList(),
        var invariantSpecs: MutableList<SMVExpr> = ArrayList(),
        var ltlSpec: MutableList<SMVExpr> = ArrayList(),
        var ctlSpec: MutableList<SMVExpr> = ArrayList(),
        var nextAssignments: MutableList<SAssignment> = ArrayList(),
        var transExpr: MutableList<SMVExpr> = ArrayList(),
        var initExpr: MutableList<SMVExpr> = ArrayList(),
        var definitions: MutableList<SAssignment> = ArrayList())
    : SMVAst() {
    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    override fun clone() = copy()
}


/**
 *
 */
data class SVariable(var name: String) : SMVExpr(), Comparable<SVariable> {
    override var dataType: SMVType? = null

    constructor(n: String, dt: SMVType) : this(n) {
        dataType = dt
    }

    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    override fun compareTo(o: SVariable): Int {
        return name.compareTo(o.name)
    }

    /*override fun toString(): String {
        return name
    }*/

    override fun clone() = copy().also { it.dataType = dataType }

    override fun inModule(module: String): SVariable {
        return SVariable.create("$module.$name").with(dataType)
    }

    infix fun assignTo(expr: SMVExpr) = SAssignment(this, expr)

    class Builder(name: String) {
        internal var v = SVariable(name)

        fun with(type: SMVType?): SVariable {
            v.dataType = type
            return v
        }

        fun with(width: Int, signed: Boolean): SVariable =
                with(SMVWordType(signed, width))

        fun withSigned(width: Int): SVariable =
                with(width, true)

        fun withUnsigned(width: Int): SVariable =
                with(width, false)

        fun asBool(): SVariable {
            return with(SMVTypes.BOOLEAN)
        }
    }

    companion object {
        fun bool(name: String) = Builder(name).asBool()
        fun create(name: String) = Builder(name)
        fun create(fmt: String, vararg values: Any): Builder {
            return create(String.format(fmt, *values))
        }
    }
}


/*
 * The order of parsing precedence for operators from high to low is:
 * 0: [ ] , [ : ]
 * 1: !
 * 2: ::
 * 3: - (unary minus)
 * 4: /
 * 6: mod
 * 7: *
 * 8: + -
 * 9: << >>
 * 10: union
 * 11: in
 * 12: = !=  <  >
 * 13: &
 * 14: | xor xnor
 * 15: (• ? • : •)
 * 16: <->
 * 17: ->
 */
enum class SBinaryOperator private constructor(private val symbol: String, private val precedence: Int) : SOperator {
    /**
     *
     */
    PLUS("+", 8),

    /**
     *
     */
    MINUS("-", 8),

    /**
     *
     */
    DIV("/", 4),

    /**
     *
     */
    MUL("*", 6),

    /**
     *
     */
    AND("&", 13),

    /**
     *
     */
    OR("|", 14),

    /**
     *
     */
    LESS_THAN("<", 12),

    /**
     *
     */
    LESS_EQUAL("<=", 12),

    /**
     *
     */
    GREATER_THAN(">", 12),

    /**
     *
     */
    GREATER_EQUAL(">=", 12),

    /**
     *
     */
    XOR("xor", 14),

    /**
     *
     */
    XNOR("xnor", 14),

    /**
     *
     */
    EQUAL("=", 12),

    /**
     *
     */
    IMPL("->", 17),

    /**
     *
     */
    EQUIV("<->", 16),

    /**
     *
     */
    NOT_EQUAL("!=", 12),

    /**
     *
     */
    MOD("mod", 5),

    /**
     *
     */
    SHL("<<", 9),

    /**
     *
     */
    SHR(">>", 9),

    WORD_CONCAT("::", 10);

    override fun precedence(): Int {
        return precedence
    }

    override fun symbol(): String {
        return symbol
    }

    companion object {

        fun findBySymbol(symbol: String): SBinaryOperator? {
            for (op in values()) {
                if (op.symbol.equals(symbol, ignoreCase = true)) {
                    return op
                }
            }
            return null
        }
    }
}


/**
 * @author Alexander Weigl
 * @version 1 (11.06.17)
 */
data class SQuantified(var operator: STemporalOperator,
                       var quantified: MutableList<SMVExpr> = ArrayList(2))
    : SMVExpr() {

    override val dataType: SMVTypes.BOOLEAN
        get() = SMVTypes.BOOLEAN

    constructor(operator: STemporalOperator, vararg expr: SMVExpr) : this(operator, Arrays.asList<SMVExpr>(*expr)) {}

    override fun inModule(module: String): SQuantified =
            SQuantified(operator,
                    ArrayList(quantified.map { a -> a.inModule(module) }))

    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    operator fun set(i: Int, value: SMVExpr): SMVExpr = quantified.set(i, value)
    operator fun get(i: Int) = quantified[i]

    override fun clone() = SQuantified(operator, quantified.map { it.clone() }.toMutableList())

}


/**
 * @author Alexander Weigl
 * @version 1 (11.06.17)
 */
enum class STemporalOperator constructor(val language: TemporalLanguage,
                                         val arity: Int,
                                         val symbol: String,
                                         val desc: String) {
    X(TemporalLanguage.LTL, 1, "X", "NEXT"),
    G(TemporalLanguage.LTL, 1, "G", "GLOBALLY"),
    F(TemporalLanguage.LTL, 1, "F", "FINALLY"),
    Y(TemporalLanguage.LTL, 1, "Y", "YESTERDAY"),
    Z(TemporalLanguage.LTL, 1, "Z", "?"),
    H(TemporalLanguage.LTL, 1, "H", "?"),
    O(TemporalLanguage.LTL, 1, "O", "ONCE"),

    U(TemporalLanguage.LTL, 2, "U", "UNTIL"),
    V(TemporalLanguage.LTL, 2, "V", "RELEASE"),
    S(TemporalLanguage.LTL, 2, "S", "SINCE"),
    T(TemporalLanguage.LTL, 2, "T", "?"),

    AU(TemporalLanguage.CTL, 2, "AU", ""),
    EU(TemporalLanguage.CTL, 2, "EU", ""),

    EG(TemporalLanguage.CTL, 2, "EG", ""),
    EF(TemporalLanguage.CTL, 2, "EF", ""),
    EX(TemporalLanguage.CTL, 2, "EX", ""),
    AG(TemporalLanguage.CTL, 2, "AG", ""),
    AF(TemporalLanguage.CTL, 2, "AF", ""),
    AX(TemporalLanguage.CTL, 2, "AX", "");

    fun arity(): Int {
        return arity
    }

    fun symbol(): String {
        return symbol
    }

    private enum class TemporalLanguage {
        LTL, CTL, PSL
    }

    companion object {

        fun valueOf(op: Token): STemporalOperator {
            return valueOf(op.text)
        }
    }
}


/**
 *
 */
data class SUnaryExpression(
        /**
         *
         */
        var operator: SUnaryOperator,
        /**
         *
         */
        var expr: SMVExpr) : SMVExpr() {

    override val dataType: SMVType?
        get() = expr.dataType

    override fun inModule(module: String): SUnaryExpression {
        return SUnaryExpression(operator, expr.inModule(module))
    }

    override fun clone() = SUnaryExpression(operator, expr.clone())

    override fun <T> accept(visitor: SMVAstVisitor<T>): T {
        return visitor.visit(this)
    }

    /*override fun toString(): String {
        return operator.symbol() + expr
    }*/
}


/**
 *
 */
enum class SUnaryOperator private constructor(private val symbol: String, private val precedence: Int) : SOperator {
    /**
     *
     */
    NEGATE("!", 1),

    /**
     *
     */
    MINUS("-", 3);

    override fun precedence(): Int {
        return precedence
    }

    override fun symbol(): String {
        return symbol
    }

    override fun toString(): String {
        return symbol()
    }
}
