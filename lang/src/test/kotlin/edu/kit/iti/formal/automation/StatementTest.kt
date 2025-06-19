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
package edu.kit.iti.formal.automation

import LoadHelp
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.MethodSource
import java.nio.file.Path

object StatementTest {
    @ParameterizedTest(name = "testParser: {0}")
    @MethodSource("getStatements")
    fun testParser(testFile: Path) {
        val parser = IEC61131Facade.getParser(CharStreams.fromPath(testFile))
        val ctx = parser.statement_list()
        Assertions.assertEquals(0, parser.numberOfSyntaxErrors.toLong())
    }

    @ParameterizedTest(name = "copy: {0}")
    @MethodSource("getStatements")
    fun testCopy(testFile: Path) {
        println("F:$testFile")
        val sl = IEC61131Facade.statements(CharStreams.fromPath(testFile))
        Assertions.assertEquals(sl, sl.clone())
    }

    @JvmStatic
    fun getStatements() = LoadHelp.getStatements()
}
