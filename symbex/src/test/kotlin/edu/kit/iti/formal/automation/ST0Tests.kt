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

import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (28.06.17)
 */
class ST0Tests {
    @Test
    fun fbEmbedding1() = assertResultST0("fbembedding_1")

    @Test
    fun structEmbedding() = assertResultST0("struct_embedding")

    private fun assertResultST0(file: String) {
        var (st, _) = IEC61131Facade.fileResolve(CharStreams.fromStream(javaClass.getResourceAsStream("$file.st")))
        val st0exp = IEC61131Facade.file(CharStreams.fromStream(javaClass.getResourceAsStream("$file.st0")))

        // val entry = Utils.findProgram(st)!!
        val simplified = SymbExFacade.simplify(st)
        Assertions.assertEquals(
            IEC61131Facade.print(st0exp, false),
            IEC61131Facade.print(simplified, false),
        )
    }
}
