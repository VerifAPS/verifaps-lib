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
import edu.kit.iti.formal.smt.SExprFacade
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory

/**
 * @author Alexander Weigl
 * @version 1 (12.12.18)
 */
class SExprFacadeTest {
    private val tests: Collection<String> = listOf(
        "abc",
        "1234",
        "def",
        "(+ 2 2 2 2 2 22 2 2 22 22)",
        "sat",
        "unsat",
        "|abc def|",
        "|def\n\nabc|",
        "(((((((((:bv) (_ BitVec 16)))))))))",
    )

    @TestFactory
    fun factory(): Collection<DynamicTest> = tests.map {
        DynamicTest.dynamicTest(it, {
            test(it)
        })
    }

    private fun test(it: String) {
        val res = SExprFacade.parseExpr(it).toString()
        Assertions.assertEquals(it, res)
    }
}