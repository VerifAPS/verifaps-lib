package edu.kit.iti.formal.smv.parser

import edu.kit.iti.formal.smv.ast.SMVExpr
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource

object GoodExpressionTest {
    @ParameterizedTest
    @MethodSource("getGoodExpressions")
    fun testParser(testExpression: String) {
        val slp = TestHelper.getParser(testExpression)
        val e = slp.expr()
        Assertions.assertEquals(0, slp.numberOfSyntaxErrors.toLong())
        val expr = e.accept(SMVTransformToAST()) as SMVExpr
        // TODO
        //String out = expr.accept(new StringPrinter());
        //System.out.println(">>> " + out);
    }

    @ParameterizedTest
    @MethodSource("getGoodExpressions")
    fun testLexer(testExpression: String) {
        val lex = SMVLexer(CharStreams.fromString(testExpression))
        lex.allTokens.forEach { t ->
            System.out.format("%6s: %-20s (%d,%d)%n",
                    lex.vocabulary.getDisplayName(t.type),
                    t.text,
                    t.line,
                    t.charPositionInLine)
        }
    }

    @ParameterizedTest
    @MethodSource("getGoodExpressions")
    fun testPrinter(testExpression: String) {
        val slp1 = TestHelper.getParser(testExpression!!)
        val e1 = slp1.expr()
        val expr1 = e1.accept(SMVTransformToAST()) as SMVExpr
        val out1 = expr1.repr()
        println(out1)


        val slp2 = TestHelper.getParser(out1)
        val e2 = slp2.expr()
        val expr2 = e2.accept(SMVTransformToAST()) as SMVExpr
        val out2 = expr2.repr()
        /*  Assertions.assertEquals(
                  testExpression!!.replace("[() ]".toRegex(), ""),
                  out2.replace("[() ]".toRegex(), ""))*/
        Assertions.assertEquals(0, slp2.numberOfSyntaxErrors.toLong())
        Assertions.assertEquals(out1, out2)
    }

    @JvmStatic
    fun getGoodExpressions() = TestHelper.loadLines("goodexpr.txt", 1)
}
