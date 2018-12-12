package edu.kit.iti.formal.smt

import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.math.BigInteger

/**
 *
 * @author Alexander Weigl
 * @version 1 (11.12.18)
 */
object SExprFacade {
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

    fun parseExpr(stream: String): SExpr = parseExpr(CharStreams.fromString(stream))

    fun sexpr(vararg args: Any) = sexpr(args.toList())

    fun sexpr(args: Collection<Any>): SList {
        val s = SList()
        args.forEach {
            s.list += when (it) {
                is SExpr -> it
                is String -> SSymbol(it)
                is Int -> SInteger(BigInteger.valueOf(it.toLong()))
                is Collection<*> -> sexpr(it)
                //is Float -> SNumber(it)
                else -> {
                    SSymbol("${it.javaClass} not supported")
                }
            }
        }
        return s
    }

}