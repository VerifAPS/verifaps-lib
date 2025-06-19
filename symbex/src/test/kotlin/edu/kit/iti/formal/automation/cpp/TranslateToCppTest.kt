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
package edu.kit.iti.formal.automation.cpp

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (09.07.19)
 */
internal class TranslateToCppTest {
    val test1 = """
        FUNCTION SEL : INT 
         VAR_INPUT b : BOOL; i1, i2 : INT; END_VAR
         IF b THEN 
           SEL := i1;
         ELSE 
           SEL := i2;
         END_IF
        END_FUNCTION 
        
        FUNCTION_BLOCK COUNTER
            VAR_INPUT I : INT; EN:BOOL; END_VAR
            VAR_OUTPUT Q : INT; END_VAR 
            IF EN THEN
                Q := Q + I;
            END_IF
        END_FUNCTION_BLOCK

        FUNCTION_BLOCK DOUBLER
            VAR_INPUT I : INT; EN:BOOL; END_VAR
            VAR_OUTPUT Q : INT; END_VAR 
            VAR C : COUNTER; END_VAR 
            C.I := 2 * I;
            C.EN := EN;
            C();
            Q := C.Q;
        END_FUNCTION_BLOCK

        PROGRAM entry 
            VAR_INPUT i : INT; END_VAR 
            VAR_OUTPUT o : INT; END_VAR 
            VAR DBL : DOUBLER; END_VAR 
            DBL.EN := TRUE;
            DBL.I := i;
            DBL();
            o := DBL.Q;
        END_PROGRAM
    """.trimIndent()

    @Test
    fun test1() {
        val (pous, error) = IEC61131Facade.fileResolve(CharStreams.fromString(test1))
        error.forEach { println(it) }
        // Assertions.assertTrue(error.isEmpty())

        // assertEquals(5, pous.size)
        val cpp = SymbExFacade.toCpp(pous, complete = true)
        println(cpp)
    }
}