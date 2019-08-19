package edu.kit.iti.formal.smv

import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.util.CodeWriter
import java.io.PrintWriter
import java.io.StringWriter
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
}

data class SMVWordType(
        val signed: Boolean,
        val width: Int) : SMVType {

    override fun valueOf(str: String) = SWordLiteral(read(str), this)

    override fun read(str: String): BigInteger {
        val re = Pattern.compile("(?<sign>-)?0(?<t>s|u)d(?<w>\\d+)_(?<v>\\d+)")
        val m = re.matcher(str)
        if (m.matches()) {
            TODO("further implement maybe call parser?")
        }
        return BigInteger.ZERO
    }

    override fun repr(): String {
        return String.format("%s word[%d]",
                if (signed) "signed"
                else "unsigned", width)
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
            else -> TODO("not implemented for ${value.javaClass}")
        }
    }
}

object SMVTypes {
    val GENERIC_ENUM = EnumType(listOf())

    object INT : SMVType {
        override fun valueOf(str: String): SLiteral {
            TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
        }

        override fun format(value: Any): String = value.toString()
        override fun read(str: String): Any = BigInteger(str)
        override fun repr(): String = "int"
    }

    object FLOAT : SMVType {
        override fun valueOf(str: String): SLiteral {
            TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
        }

        override fun format(value: Any) = value.toString()
        override fun read(str: String) = BigDecimal(str)
        override fun repr(): String = "real"
    }

    object BOOLEAN : SMVType {
        override fun valueOf(str: String): SLiteral {
            TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
        }

        override fun format(value: Any): String = value.toString().toUpperCase()
        override fun read(str: String): Any = str.equals("TRUE", true)
        override fun repr(): String = "boolean"
    }

    @JvmStatic
    fun infer(list: List<SMVType>): SMVType? {
        return if (list.stream().allMatch { a -> a == list[0] }) list[0] else null
    }

    @JvmStatic
    fun infer(a: SMVType, b: SMVType): SMVType? {
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

    override fun valueOf(value: String): SLiteral {
        if (!values.contains(value)) {
            throw IllegalArgumentException()
        }
        return SEnumLiteral(value, this)
    }

    override fun toString(): String {
        return if (values.isEmpty()) "{}"
        else
            values.joinToString(", ", "{", "}") { format(it) }
    }
}

data class ModuleType(
        val moduleName: String
        , val parameters: List<SMVExpr>
) : SMVType {
    override fun format(value: Any): String = TODO("not implemented")
    override fun read(str: String): Any = TODO("not implemented")
    override fun valueOf(str: String): SLiteral = TODO()
    override fun repr(): String = toString()

    constructor(name: String, vararg variables: SVariable) :
            this(name, Arrays.asList<SVariable>(*variables))

    override fun toString(): String {
        val stream = StringWriter()
        val printer = SMVPrinter(CodeWriter(stream))
        return String.format("${moduleName}(%s)",
                if (parameters.size > 0) {
                    parameters.joinToString(", ") { it.repr() }
                } else "")
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
