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
package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.util.CodeWriter
import org.jdom2.Element

/**
 * @author Alexander Weigl
 * @version 1 (30.05.17)
 */
class SFCFactory(sfcElement: Element, internal val writer: CodeWriter) {
    val access = SfcElementAccess(sfcElement)

    /* nodes:         step, macroStep, transition, selectionDivergence
        selectionConvergence, simultaneousDivergence, simultaneousConvergence */
    val handledNodes = arrayListOf<String>()

    fun run() {
        access.steps.forEach {
            writeStep(it)
            handledNodes.add(it.localId)
        }

        (access.pfork + access.pjoin).forEach { n ->
            n.transitions.forEach {
                handledNodes += it.usedNodes
                writeTransition(it.from, it.to, it.condition)
            }
        }

        (access.sfork + access.sjoin).forEach { n ->
            n.transitions.forEach {
                handledNodes += it.usedNodes
                writeTransition(it.from, it.to, it.condition)
            }
        }
        access.transitions
            .filter { it.localId !in handledNodes }
            .forEach { t ->
                t.transitions.forEach {
                    writeTransition(it.from, it.to, it.condition)
                    handledNodes += it.usedNodes
                }
            }

        println(handledNodes)
    }

    private fun writeTransition(from: Collection<String>, to: Collection<String>, condition: Collection<String>) {
        writeTransition(
            from.joinToString(", ", "(", ")"),
            to.joinToString(", ", "(", ")"),
            condition.joinToString(", ", "(", ")"),
        )
    }

    private fun writeTransition(from: String, to: String, condition: String) {
        if (condition == "()") {
            // If a transition has no condition it is hidden in the diagram.
            // This occurs, for example if you make jumps into simultaneous divergence.
            // Then a sim. convergence is added, which has transition to all "open" ends with no guard.
            // I hate PCLOpenXML. Why not protobuf!
            return
        }
        writer.nl().printf("TRANSITION FROM $from TO $to := $condition; END_TRANSITION")
    }

    private fun writeStep(step: SfcElementAccess.Step) {
        writer.nl().nl()
        if (step.initial) writer.printf("INITIAL_")
        writer.printf("STEP ${step.name} : (*Local Id: ${step.localId} *)")
        writer.block {
            step.onEntry?.let { writer.nl().printf("$it($QUALIFIER_ONENTRY);") }
            step.onExit?.let { writer.nl().printf("$it(${QUALIFIER_ONEXIT});") }
            step.onWhile?.let { writer.nl().printf("$it($QUALIFIER_ONWHILE);") }

            step.actionBlock?.let {
                // TODO            writer.printf("(* TODO handle action blocks *)")
            }
        }
        writer.nl().printf("END_STEP")
    }
}

const val QUALIFIER_ONENTRY = "P0"
const val QUALIFIER_ONEXIT = "P1"
const val QUALIFIER_ONWHILE = "N"