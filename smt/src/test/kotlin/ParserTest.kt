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
import edu.kit.iti.formal.smt.readFirstSexpr
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import java.io.StringReader

/**
 * @author Alexander Weigl
 * @version 1 (11.12.18)
 */
class ParserTest {
    @TestFactory
    fun testReadFirstSexpr(): Collection<DynamicTest> = listOf(
        testReadFirstSexpr("abc", "abc"),
        testReadFirstSexpr("abc", "abc def"),
        testReadFirstSexpr("|abc|", "     |abc|"),
        testReadFirstSexpr("|ab c|", "     |ab c|"),
        testReadFirstSexpr("(abc)", "(abc) def"),
        testReadFirstSexpr("(123 (456))", "(123 (456)) 2423424"),
        testReadFirstSexpr("(123 (456) 789)", "(123 (456) 789) 2423424"),
        testReadFirstSexpr("abc", "abc (123 (456) 789) 2423424"),
    )

    fun testReadFirstSexpr(exp: String, input: String): DynamicTest = DynamicTest.dynamicTest(exp) { Assertions.assertEquals(exp, getSexpr(input)) }

    fun getSexpr(s: String): String = readFirstSexpr(StringReader(s))
}
