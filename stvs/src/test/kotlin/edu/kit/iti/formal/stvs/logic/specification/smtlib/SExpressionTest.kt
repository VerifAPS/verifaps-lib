package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.smt.SExpr
import edu.kit.iti.formal.smt.SExprFacade.parseExpr
import edu.kit.iti.formal.smt.SExprFacade.sexpr
import edu.kit.iti.formal.smt.SList
import edu.kit.iti.formal.smt.SSymbol
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import kotlin.test.assertFailsWith

internal fun fromText(s: String) = parseExpr(s)

/**
 * Created by csicar on 08.02.17.
 */
class SExpressionTest {
    @Test
    fun fromString() {
        assertEquals(
            SList(
                "a", SSymbol("b"), SSymbol("c"),
                sexpr("nested1", "2", "3"),
                SList("4")
            ),
            fromText("(a b c (nested1 2 3 ) (4))")
        )
    }


    @Test
    fun fromStringWrongInput() {
        assertFailsWith<IllegalArgumentException> {
            fromText(")asdasd")
        }
    }

    @ParameterizedTest
    @MethodSource("instancesToTest")
    fun toText(expression: SExpr) {
        assertEquals(expression, fromText(expression.toString()))
    }

    @ParameterizedTest
    @MethodSource("instancesToTest")
    fun testEquals(expression: SExpr) {
        assertNotEquals(expression, this)
        assertEquals(expression, expression)
        assertFalse(false)
    }

    companion object {
        @JvmStatic
        fun instancesToTest(): List<Arguments> {
            val list = SList("a", SSymbol("b"), SSymbol("c"), sexpr("n1", "n2"))
            return listOf(
                Arguments.of(list),
                Arguments.of(SSymbol("asdasd")),
                Arguments.of(SSymbol("1"))
            )
        }
    }
}