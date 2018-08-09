package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.util.CodeWriter
import org.jdom2.Element

/**
 * @author Alexander Weigl
 * @version 1 (30.05.17)
 */
class SFCFactory(internal val sfcElement: Element,
                 internal val writer: CodeWriter) {
    val access = SfcElementAccess(sfcElement)

    /*    /**
        step, macroStep, transition, selectionDivergence
        selectionConvergence, simultaneousDivergence, simultaneousConvergence
         */
        */
    val handledNodes = arrayListOf<String>()

    fun run() {
        access.steps.forEach { writeStep(it); handledNodes.add(it.localId) }

        (access.pfork + access.pjoin).forEach {
            it.transitions.forEach {
                handledNodes += it.usedNodes
                writeTransition(it.from, it.to, it.condition)
            }
        }

        (access.sfork + access.sjoin).forEach {
            it.transitions.forEach {
                handledNodes += it.usedNodes
                writeTransition(it.from, it.to, it.condition)
            }
        }
        access.transitions
                .filter { it.localId !in handledNodes }
                .forEach {
                    it.transitions.forEach {
                        writeTransition(it.from, it.to, it.condition);
                        handledNodes += it.usedNodes
                    }
                }

        println(handledNodes)
    }

    private fun writeTransition(from: Collection<String>, to: Collection<String>, condition: Collection<String>) {
        writeTransition(from.joinToString(", ", "(", ")"),
                to.joinToString(", ", "(", ")"),
                condition.joinToString(", ", "(", ")"))
    }

    private fun writeTransition(from: String, to: String, condition: String) {
        writer.nl().printf("TRANSITION FROM $from TO $to := $condition END_TRANSITION")
    }

    val QUALIFIER_ONENTRY = "P0"
    val QUALIFIER_ONEXIT = "P1"
    val QUALIFIER_ONWHILE = "N"

    private fun writeStep(step: SfcElementAccess.Step) {
        writer.nl().nl()
        if (step.initial) writer.printf("INITIAL_")
        writer.printf("STEP ${step.name} : (*Local Id: ${step.localId} *)")
        writer.block {
            step.onEntry?.let { writer.nl().printf("$it($QUALIFIER_ONENTRY);") }
            step.onExit?.let { writer.nl().printf("$it(${QUALIFIER_ONEXIT});") }
            step.onWhile?.let { writer.nl().printf("$it($QUALIFIER_ONWHILE);") }

            step.actionBlock?.let {
                //TODO            writer.printf("(* TODO handle action blocks *)")
            }
        }
        writer.nl().printf("END_STEP")
    }
}

