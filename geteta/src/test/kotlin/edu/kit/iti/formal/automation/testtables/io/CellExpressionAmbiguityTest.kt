/**
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl></weigl>@kit.edu>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http:></http:>//www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.io


import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.exception.ProgramAbortionException
import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import org.junit.Assert
import org.junit.Test

/**
 * Created by weigl on 15.12.16.
 */
class CellExpressionAmbiguityTest {

    @Test
    fun testBoolean() {
        val v = SVariable.create("a").asBool()
        Assert.assertEquals(
                SLiteral.TRUE.equal(v),
                parse("TRUE")
        )
    }

    @Test
    fun testReference() {
        Assert.assertEquals(
                SVariable.create("_0\$b__history._$2").withUnsigned(16)
                        .equal(defaultVar()),
                parse("b[-2]")
        )
    }


    @Test(expected = ProgramAbortionException::class)
    fun testInvalidReferencePositive() {
        GetetaFacade.exprToSMV("b[2]",
                SVariable.create("a").asBool(), 0, pc)
    }


    @Test
    fun testValidReferenceZero() {
        GetetaFacade.exprToSMV("b[0]", SVariable.create("a").asBool(), 0, pc)
    }

    companion object {
        val pc = CellExpressionTest.defaultTestTable().parseContext

        fun parse(cell: String): SMVExpr {
            return GetetaFacade.exprToSMV(cell, defaultVar(), 0, pc)
        }

        private fun defaultVar(): SVariable {
            return SVariable.create("a").asBool()
        }
    }

}
