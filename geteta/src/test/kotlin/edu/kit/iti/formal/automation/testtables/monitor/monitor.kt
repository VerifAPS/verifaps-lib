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
package edu.kit.iti.formal.automation.testtables.monitor

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.Test
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (14.07.19)
 */
class MonitorTests {
    @Test
    fun testSimple() {
        val file = File("examples/constantprogram/constantprogram.gtt")
        Assumptions.assumeTrue(file.exists())
        val gtt = GetetaFacade.parseTableDSL(file).first()
        gtt.programRuns += ""
        gtt.generateSmvExpression()
        val automaton = GetetaFacade.constructTable(gtt).automaton
        val mon = CppMonitorGenerator.generate(gtt, automaton)
        println(mon)
    }
}