/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.stvs.logic.specification.smtlib

import com.google.common.truth.Truth.assertThat
import edu.kit.iti.formal.smt.SExpr
import edu.kit.iti.formal.smt.SExprFacade.parseExpr
import edu.kit.iti.formal.smt.SExprFacade.sexpr
import edu.kit.iti.formal.smt.SList
import edu.kit.iti.formal.smt.SNumber
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
        assertThat(SSymbol("a")).isEqualTo(SSymbol("a"))
        assertThat(SList(SSymbol("a"))).isEqualTo(SList(SSymbol("a")))
        assertThat(fromText("a")).isEqualTo(SSymbol("a"))
        assertThat(fromText("()")).isEqualTo(SList())
        assertThat(fromText("(a)")).isEqualTo(SList(SSymbol("a")))

        assertThat(fromText("(nested1 2 3)"))
            .isEqualTo(sexpr("nested1", 2, 3))

        assertThat(
            fromText("(a b c (nested1 2 3 ) (4))"),
        ).isEqualTo(
            SList(
                "a",
                SSymbol("b"),
                SSymbol("c"),
                sexpr("nested1", 2, 3),
                SList(SNumber(4)),
            ),
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
        assertThat(fromText(expression.toString())).isEqualTo(expression)
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
                Arguments.of(SNumber(1)),
            )
        }
    }
}