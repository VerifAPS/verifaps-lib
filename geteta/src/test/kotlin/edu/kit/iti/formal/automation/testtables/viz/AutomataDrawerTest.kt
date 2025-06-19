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
package edu.kit.iti.formal.automation.testtables.viz

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.builder.AutomatonBuilderPipeline
import org.junit.jupiter.api.Test
import java.io.File

/**
 * @author Alexander Weigl
 * @version 1 (08.08.18)
 */
class AutomataDrawerTest {
    @Test
    fun testSimple() = renderAndShow("examples/NewFile.gtt")

    @Test
    fun testMinMax() = renderAndShow("examples/MinMax/MinMax.tt.txt")

    private fun renderAndShow(file: String) {
        val tt = GetetaFacade.readTables(File(file)).first()
        val pip = AutomatonBuilderPipeline(tt)
        val auto = pip.transform()
        val ad = AutomatonDrawer(File("tmp.dot"), listOf(tt.region), auto.automaton)
        ad.runDot = true
        ad.show = true
        ad.run()
    }
}