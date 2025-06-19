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

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.util.CodeWriter
import java.io.StringWriter

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.09.18)
 */
object MonitorGenerationEsterel : MonitorGeneration {
    override val key = "esterel"
    override fun generate(gtt: GeneralizedTestTable, automaton: TestTableAutomaton, options: MonitorGenerationOptions) = Monitor(body = Impl(gtt, automaton).call())

    internal class Impl(
        private val gtt: GeneralizedTestTable,
        private val automaton: TestTableAutomaton,
    ) {

        var moduleName = "monitor"

        fun call(): String {
            val stream = StringWriter()
            val out = CodeWriter(stream)
            out.write("module $moduleName : ").block {
                out.nl().print("input ")
                gtt.programVariables.joinTo(out, ", ") { it.name }
                out.print(";")

                out.nl().print("signal ")
            }
            return stream.toString()
        }
    }
}
