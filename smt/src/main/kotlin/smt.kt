package edu.kit.iti.formal.smt

import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.math.BigInteger


/**
 *
 * @author Alexander Weigl
 * @version 1 (13.10.18)
 */
sealed class SExpr {
    abstract val isAtom: Boolean
    abstract override fun toString(): String
}

abstract class SAtom() : SExpr() {
    override val isAtom: Boolean
        get() = true
}

data class SInteger(var num: BigInteger) : SAtom() {
    constructor(numnum: Int) : this(numnum.toBigInteger())

    override fun toString() = num.toString()
}

data class SBitVector(var num: BigInteger, var bitSize: Int) : SAtom() {
    override fun toString() = "#x" + SmtFacade.hexFromInt(num, bitSize)
}

data class SSymbol(var text: String) : SAtom() {
    init {
        text = text.trim('|')
    }

    override fun toString() = "|$text|"
}

data class SList(internal val list: ArrayList<SExpr> = ArrayList()) : MutableList<SExpr> by list, SExpr() {
    constructor(list: List<SExpr>) : this(ArrayList(list))
    constructor(vararg args: SExpr) : this() {
        args.forEach { add(it) }
    }
    constructor(symbol: String, vararg args: SExpr) : this() {
        add(SSymbol(symbol))
        args.forEach { add(it) }
    }
    constructor(symbol: String, args: List<SExpr>) : this() {
        list += SSymbol(symbol)
        list.addAll(args)
    }

    override val isAtom: Boolean
        get() = false

    override fun toString() = list
            .joinToString(" ", "(", ")") { it.toString() }
}

object SmtFacade {
    fun createParser(stream: CharStream): SexprParser {
        val lexer = SexprLexer(stream)
        val parser = SexprParser(CommonTokenStream(lexer))
        return parser
    }

    fun createParser(stream: String) = createParser(CharStreams.fromString(stream))

    fun parse(stream: CharStream): ArrayList<SExpr> {
        val p = createParser(stream)
        val ctx = p.file()
        val t = SexprParseTreeTransformer()
        val ast = ctx.accept(t) as SList
        return ast.list
    }

    fun parseExpr(stream: CharStream): SExpr {
        val p = createParser(stream)
        val ctx = p.sexpr()
        val t = SexprParseTreeTransformer()
        return ctx.accept(t)
    }


    /**
     * Convert an integer to its hex representation. The bitLength specifies the number of output digits.
     * e.g. a bitLength of 2 lets you convert positive numbers between 0 an 255 or numbers between -128
     * and 127 to their text representation Numbers are represented as a hexadecimal two's
     * complement.
     *
     * @param integer arbitrary integer
     * @param bitLength Number of digits of output
     * @return hex representation with following format: #xABCD...
     */
    fun hexFromInt(integer: BigInteger, bitLength: Int): String {
        val number = integer.toByteArray()
        val byteLength = bitLength / 8
        /*if (number.size > byteLength) {
            throw IllegalArgumentException("bit length is too small for $integer")
        }*/
        val neg = integer.signum() < 0
        val offset = byteLength - number.size
        val out = IntArray(byteLength) {
            val p = it - offset
            val b = if (p >= 0) number[p].toInt() else if (neg) 255 else 0
            if (b < 0) b + 256 else b
        }

        return "#x" + out.joinToString("") {
            String.format("%02X", it)
        }
    }

    /**
     * Converts a hex representation (hexadecimal two's complement) of an integer to an integer.
     *
     * @param hex hex representation with following format: #xABCD...
     * @param signed Defines if `hex` should be interpreted signed.
     * @return converted number
     */
    fun intFromHex(hex: String, signed: Boolean): Int {
        val isBinary = hex.startsWith("#b")
        val isHex = hex.startsWith("#x")
        val value = hex.trim('#', 'b', 'x')
        var result = 0
        for (i in 0 until hex.length) {
            result *= 16
            result += Integer.parseInt(hex[i] + "", 16)
        }
        val full = Math.pow(16.0, hex.length.toDouble()).toInt()
        if (result >= full / 2 && signed) {
            result = -(full - result)
        }
        return result
    }
}

class SexprParseTreeTransformer : SexprBaseVisitor<SExpr>() {
    override fun visitFile(ctx: SexprParser.FileContext): SExpr {
        val expressions = ctx.sexpr().map { it.accept(this) }
        return SList(expressions)
    }

    override fun visitN(ctx: SexprParser.NContext) = SInteger(BigInteger(ctx.NUMBER().text))

    override fun visitS(ctx: SexprParser.SContext) = SSymbol(ctx.SYMBOL().text)

    override fun visitList(ctx: SexprParser.ListContext?): SExpr {

        return super.visitList(ctx)
    }
}