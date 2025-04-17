package edu.kit.iti.formal.smv

import edu.kit.iti.formal.smv.ast.*
import java.math.BigDecimal
import java.math.BigInteger
import java.util.*
import java.util.regex.Pattern

/**
 *
 * @author Alexander Weigl
 * @version 1 (09.04.18)
 */

interface SMVType {
    fun format(value: Any): String
    fun read(str: String): Any
    fun valueOf(str: String): SLiteral
    fun repr(): String
    fun allowedValue(obj: Any): Boolean
}

data class SMVWordType(
        val signed: Boolean,
        val width: Int) : SMVType {

    override fun valueOf(str: String) = SWordLiteral(read(str), this)

    override fun read(str: String): BigInteger {
        val re = Pattern.compile("(?<sign>-)?0(?<t>[su])d(?<w>\\d+)_(?<v>\\d+)")
        val m = re.matcher(str)
        if (m.matches()) {
            val word = SMVFacade.parseWordLiteral(str)
            return word.value
        }
        return BigInteger.ZERO
    }

    override fun repr(): String {
        return String.format("%s word[%d]",
                if (signed) "signed"
                else "unsigned", width)
    }

    override fun allowedValue(obj: Any): Boolean {
        return obj is BigInteger
    }

    override fun format(value: Any): String {
        return when (value) {
            is BigInteger ->
                String.format("%s0%sd%d_%s",
                        if (value.signum() < 0) "-" else "",
                        if (signed) "s" else "u",
                        width,
                        value.abs().toString())
            is Long -> format(BigInteger.valueOf(value))
            is Int -> format(BigInteger.valueOf(value.toLong()))
            else -> error("not implemented for ${value.javaClass}")
        }
    }
}

object SMVTypes {
    val GENERIC_ENUM = EnumType(listOf())

    object INT : SMVType {
        override fun valueOf(str: String): SLiteral = SIntegerLiteral(BigInteger(str))
        override fun format(value: Any): String = value.toString()
        override fun read(str: String): Any = BigInteger(str)
        override fun repr(): String = "int"
        override fun allowedValue(obj: Any): Boolean = obj is BigInteger
    }

    object FLOAT : SMVType {
        override fun valueOf(str: String): SLiteral = SFloatLiteral(BigDecimal(str))
        override fun format(value: Any) = value.toString()
        override fun read(str: String) = BigDecimal(str)
        override fun repr(): String = "real"
        override fun allowedValue(obj: Any): Boolean = obj is BigDecimal
    }

    object BOOLEAN : SMVType {
        override fun valueOf(str: String) = if (str.equals("true", true)) SLiteral.TRUE else SLiteral.FALSE
        override fun format(value: Any): String = value.toString().uppercase(Locale.getDefault())
        override fun read(str: String): Any = str.equals("TRUE", true)
        override fun repr(): String = "boolean"
        override fun allowedValue(obj: Any): Boolean = obj is Boolean
    }

    @JvmStatic
    fun infer(list: List<SMVType>): SMVType? {
        return if (list.stream().allMatch { a -> a == list[0] }) list[0] else null
    }


    @JvmStatic
    fun infer(op: SBinaryOperator, a: SMVType?, b: SMVType?): SMVType? {
        return when (op) {
            SBinaryOperator.AND -> BOOLEAN
            SBinaryOperator.OR -> BOOLEAN
            SBinaryOperator.LESS_THAN -> BOOLEAN
            SBinaryOperator.LESS_EQUAL -> BOOLEAN
            SBinaryOperator.GREATER_THAN -> BOOLEAN
            SBinaryOperator.GREATER_EQUAL -> BOOLEAN
            SBinaryOperator.XOR -> BOOLEAN
            SBinaryOperator.XNOR -> BOOLEAN
            SBinaryOperator.EQUAL -> BOOLEAN
            SBinaryOperator.IMPL -> BOOLEAN
            SBinaryOperator.EQUIV -> BOOLEAN
            SBinaryOperator.NOT_EQUAL -> BOOLEAN
            SBinaryOperator.WORD_CONCAT -> TODO()
            else -> infer(a, b)
        }
    }

    @JvmStatic
    fun infer(a: SMVType?, b: SMVType?): SMVType? {
        return if (a == b) a else null
    }

    @JvmStatic
    fun unsigned(i: Int): SMVWordType {
        return SMVWordType(false, i)
    }

    @JvmStatic
    fun signed(i: Int): SMVWordType {
        return SMVWordType(true, i)
    }
}

data class EnumType(var values: List<String>) : SMVType {
    override fun format(value: Any): String = SMVPrinter.quoted(value.toString())
    override fun read(str: String): String = str
    override fun repr(): String = toString()

    override fun allowedValue(obj: Any): Boolean = obj is String

    override fun valueOf(str: String): SLiteral {
        if (!values.contains(str)) {
            throw IllegalArgumentException()
        }
        return SEnumLiteral(str, this)
    }

    override fun toString(): String {
        return if (values.isEmpty()) "{}"
        else
            values.joinToString(", ", "{", "}") { format(it) }
    }
}

data class ModuleType(val moduleName: String, val parameters: List<SMVExpr>
) : SMVType {
    override fun format(value: Any): String = error("not implemented")
    override fun read(str: String): Any = error("not implemented")
    override fun valueOf(str: String): SLiteral = error("not implemented")
    override fun repr(): String = toString()

    override fun allowedValue(obj: Any): Boolean = obj is String

    constructor(name: String, vararg variables: SVariable) :
            this(name, Arrays.asList<SVariable>(*variables))

    override fun toString(): String {
        val params = if (parameters.isNotEmpty()) {
            parameters.joinToString(", ") { it.repr() }
        } else ""
        return "${moduleName}($params)"

    }
}



/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
typealias FunctionTypeSolver = (SFunction) -> SMVType?

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
object FunctionTypeSolvers {
    val FIRST_ARGUMENT: FunctionTypeSolver = { it.arguments[0].dataType }
    val LAST_ARGUMENT: FunctionTypeSolver = { it.arguments[it.arguments.size - 1].dataType }

    val TO_SIGNED = { f: SFunction ->
        val (_, width) = FIRST_ARGUMENT(f) as SMVWordType
        SMVWordType(true, width)
    }

    val TO_UNSIGNED = { f: SFunction ->
        val (_, width) = FIRST_ARGUMENT(f) as SMVWordType
        SMVWordType(false, width)
    }

    fun specificType(dt: SMVType): FunctionTypeSolver = { dt }
}
