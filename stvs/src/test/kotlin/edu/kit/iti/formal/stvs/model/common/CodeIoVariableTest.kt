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
package edu.kit.iti.formal.stvs.model.common

import org.junit.Assert
import org.junit.jupiter.api.Test

/**
 * Created by Lukas on 22.02.2017.
 *
 * @author Lukas
 */
class CodeIoVariableTest {
    private val var1 = CodeIoVariable(VariableCategory.INPUT, "BOOL", "var")
    private val var2 = CodeIoVariable(VariableCategory.INPUT, "BOOL", "var")
    private val `object` = Any()

    @Test
    @Throws(Exception::class)
    fun equalsCodeIoVariable() {
        Assert.assertTrue(var1 == var2)
        Assert.assertNotEquals(CodeIoVariable(VariableCategory.INPUT, "INT", "var"), var2)
    }

    @Test
    fun testHashCode() {
        Assert.assertEquals(var1.hashCode().toLong(), var2.hashCode().toLong())
        Assert.assertNotEquals(
            CodeIoVariable(VariableCategory.INPUT, "INT", "var").hashCode().toLong(),
            var2.hashCode().toLong(),
        )
    }

    @Test
    @Throws(Exception::class)
    fun equalsObject() {
        Assert.assertTrue(var1 != `object`)
    }
}