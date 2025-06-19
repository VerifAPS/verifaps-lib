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
package edu.kit.iti.formal.automation.testtables.apps

import org.junit.jupiter.api.Test
import java.io.StringWriter

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/25/20)
 */
internal class CsvTranslatorTest {
    @Test fun simpleTest() {
        val csvInput = """
            in I : INT,out O : BOOL,DURATION
            =2,=TRUE, 1
            =I[-1],-,>=0
            =2+2, =I>5,"[3,5]"
            "=2+2,I%2=0",-,omega
        """.trimIndent()

        val out = StringWriter()
        val t = CsvTranslator(out, "\"", ",")
        t.run("test", csvInput)
        println(out.toString())
    }
}
