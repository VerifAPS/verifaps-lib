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
package edu.kit.iti.formal.automation.smt

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Test
import java.io.FileInputStream
import java.io.IOException

/**
 * @author Alexander Weigl
 * @version 1 (16.10.17)
 */
class SmtFacadeTest {
    @Test
    @Throws(IOException::class)
    fun testTranslateTrafficLights() {
        /*InputStream isType = getClass().getResourceAsStream(
                "traffic_light_bools.st");*/
        val `is` = FileInputStream("src/test/resources/traffic_light_bools.st")
        val code = IEC61131Facade.file(CharStreams.fromStream(`is`))
        IEC61131Facade.resolveDataTypes(code)
        val symplifiedCode = SymbExFacade.simplify(code)
        val module = SymbExFacade.evaluateProgram(symplifiedCode)
        val program = SmvSmtFacade.translate(module)
        println(program.preamble)
        println(program.getStepDefinition(true, "", "_0"))
        println(program.getStepDefinition(false, "", "_1"))
        println(program.getAssertInit("_0"))
        println(program.getAssertNext("_0", "_1"))
    }
}
