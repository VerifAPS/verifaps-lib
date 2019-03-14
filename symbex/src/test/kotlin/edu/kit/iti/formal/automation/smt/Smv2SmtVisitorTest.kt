package edu.kit.iti.formal.automation.smt

import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.smv.ast.SMVAst
import org.junit.jupiter.api.Assertions
 import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (12.12.18)
 */
class Smv2SmtVisitorTest {
    @Test
    fun test1(): Unit {
        test("false", SLiteral.FALSE)
        test("true", SLiteral.TRUE)
    }

    private fun test(exp: String, smv: SMVAst) {
        val v = Smv2SmtVisitor(fnTranslator = DefaultS2SFunctionTranslator(), dtTranslator = DefaultS2STranslator(),
                statePrefix = "")
        val res = smv.accept(v)
        Assertions.assertEquals(exp, res.toString())
    }
}