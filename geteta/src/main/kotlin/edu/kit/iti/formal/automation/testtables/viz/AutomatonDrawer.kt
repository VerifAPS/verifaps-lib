package edu.kit.iti.formal.automation.testtables.viz

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.Region
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.automata.AutomatonState
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.automation.testtables.model.automata.Transition
import edu.kit.iti.formal.automation.testtables.model.automata.TransitionType
import edu.kit.iti.formal.util.CodeWriter
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (07.03.18)
 */
class AutomatonDrawer(val outputFile: File,
                      val gtt: GeneralizedTestTable,
                      val automata: TestTableAutomaton) : Runnable {

    var runDot: Boolean = false

    var show: Boolean = false

    var useCluster = true

    var useClusterForRows = false

    val attributes: MutableMap<AutomatonState, MutableMap<String, String>> = HashMap()

    fun addAttribute(state: AutomatonState, name: String, value: String) {
        attributes.computeIfAbsent(state) { HashMap() }[name] = "\"$value\""
    }

    fun addAttribute(state: AutomatonState, vararg kv: Pair<String, String>) {
        val map = attributes.computeIfAbsent(state) { HashMap() }
        kv.forEach { (k, v) ->
            map[k] = "\"$v\""
        }
    }

    init {
        automata.rowStates.values.flatMap { it }.forEach {
            addAttribute(it, "label", "${it.row.id}@${it.time}")
        }

        automata.initialStates.forEach {
            addAttribute(it, "shape", "rectangle")
            addAttribute(it, "color", "blue")
        }

        addAttribute(automata.stateError, "shape" to "doublecircle", "label" to "error", "color" to "red")
        addAttribute(automata.stateSentinel, "shape" to "septagon", "label" to "end", "color" to "green")
    }

    override fun run() {
        outputFile.bufferedWriter().use {
            createDot(CodeWriter(it))
        }
        if (runDot) {
            if (doDot() && show) doShow()
        }
    }

    private fun createDot(writer: CodeWriter) {
        writer.print("digraph G {")
                .increaseIndent()
                .nl()
                .println("rankdir=LR;")

        if (useCluster)
            addStates(gtt.region, writer)
        else
            automata.rowStates.values.flatMap { it }
                    .joinTo(writer, "\n") {
                        state(it)
                    }


        writer.write(state(automata.stateError) + "\n")
        writer.write(state(automata.stateSentinel) + "\n")

        automata.transitions.joinTo(writer, "\n") { transition(it) }

        writer.write("\n}")

    }

    private fun addStates(region: Region, writer: CodeWriter) {
        writer.nl().print("subgraph cluster${region.id} {").increaseIndent()
        region.children.forEach {
            when (it) {
                is Region -> addStates(it, writer)
                is TableRow -> addStates(it, writer)
            }
        }
        writer.nl().print("label=\"group ${region.id} (${region.duration})\";")
                .nl().print("color=black; attributes=dotted;")
                .nl().decreaseIndent().nl().write("}").nl()
    }

    private fun addStates(row: TableRow, writer: CodeWriter) {
        if (useClusterForRows)
            writer.nl().print("subgraph cluster${row.id} {").increaseIndent()

        automata.getStates(row)?.forEach { writer.nl().print(state(it)) }

        if (useClusterForRows)
            writer.nl().print("label=\"row ${row.id} (${row.duration})\";")
                    .nl().print("color=grey; attributes=dashed;")
                    .nl().decreaseIndent().nl().write("}").nl()
    }

    private fun transition(t: Transition): String {
        val color =
                when(t.type) {
                    TransitionType.FWD ->"green"
                    TransitionType.FAIL->"red"
                    else -> "black"
                }

        return "\t${t.from.name} -> ${t.to.name} [label=\"${t.type}\",color=$color]"
    }

    fun state(s: AutomatonState): String {
        val a = attributes[s]?.entries?.joinToString(",") { (k, v) -> "$k=$v" }
        return "\t${s.name} [$a];"
    }


    val tmpFile = File.createTempFile(outputFile.nameWithoutExtension, ".pdf")

    private fun doDot(): Boolean {
        val pb = ProcessBuilder("dot", "-Tpdf", "-o", tmpFile.absolutePath, outputFile.absolutePath)
                .inheritIO()
        println(pb.command())
        val rt = pb.start()
                .waitFor()
        return rt == 0
    }

    private fun doShow(): Boolean {
        val rt = ProcessBuilder("xdg-open", tmpFile.absolutePath)
                .inheritIO()
                .start()
                .waitFor()
        return rt == 0
    }

}