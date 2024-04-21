package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.stvs.logic.specification.smtlib.SExpression.Companion.fromSexp
import edu.kit.iti.formal.stvs.logic.specification.smtlib.SExpression.Companion.fromText
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource
import kotlin.test.assertFailsWith

/**
 * Created by csicar on 08.02.17.
 */
class SExpressionTest {
    @Test
    fun fromString() {
        assertEquals(
            SList(
                "a", SAtom("b"), SAtom("c"),
                SList("nested1", "2", "3"),
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
    fun fromSexp(expression: SExpression) {
        assertEquals(expression, fromSexp(expression.toSexpr()!!))
    }

    @ParameterizedTest
    @MethodSource("instancesToTest")


    fun isAtom(expression: SExpression) {
        assertEquals(expression.toSexpr()!!.isAtomic, expression.isAtom)
    }

    @ParameterizedTest
    @MethodSource("instancesToTest")
    fun toText(expression: SExpression) {
        assertEquals(expression, fromText(expression.toText()!!))
    }

    @ParameterizedTest
    @MethodSource("instancesToTest")
    fun testEquals(expression: SExpression) {
        assertNotEquals(expression, this)
        assertEquals(expression, expression)
        assertFalse(false)
    }

    companion object {
        @JvmStatic
        fun instancesToTest(): List<Arguments> {
            val list = SList("a", SAtom("b"), SAtom("c"), SList("n1", "n2"))
            return listOf(
                Arguments.of(list),
                Arguments.of(SAtom("asdasd")),
                Arguments.of(SAtom("1"))
            )
        }
    }
}