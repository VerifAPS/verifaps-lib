package edu.kit.iti.formal.automation.testtables.viz

import edu.kit.iti.formal.automation.VisualizeTrace
import edu.kit.iti.formal.automation.rvt.LineMap
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.smv.CounterExample
import edu.kit.iti.formal.util.CodeWriter

class CounterExamplePrinterWithProgram(
    val automaton: TestTableAutomaton,
    val testTable: GeneralizedTestTable,
    val cex: CounterExample,
    lineMap: LineMap,
    val program: PouExecutable,
    val stream: CodeWriter = CodeWriter()
) {

    val vt = VisualizeTrace(cex, lineMap, program, stream).also { vt ->
        vt.programVariableToSVar = { "code$.${it}" }
    }

    fun getAll() {
        for (k in 0 until cex.stateSize - 1) {
            get(k)
        }
    }


    fun get(k: Int) {
        vt.get(k, k + 1)
        printAssertions(k)
    }

    private fun printAssertions(k: Int) {
        stream.print(" * Table rows:").nl()
        printVariables(k)
    }

    private fun printVariables(k: Int) {
        testTable.region.flat()
            .forEach { row ->
                val activateStates = isRowActive(k, row)
                val rowActive = if (activateStates.isNotEmpty()) OKMARK else ERRMARK
                val prfx = "_${testTable.name}."
                val assumption = prfx + row.defInput.name
                val assertion = prfx + row.defOutput.name
                val fwd = prfx + row.defForward.name

                val times = activateStates.joinToString(", ") { it.toString() }

                stream.print(
                    " *     $rowActive Row ${row.id} " +
                            "${boolForHuman(k, assumption)} --> ${boolForHuman(k, assertion)}:" +
                            " ${boolForHuman(k, fwd)} (Time: $times)"
                ).nl()
            }
    }

    private fun boolForHuman(k: Int, n: String): Char {
        val v = cex[k, n]
        val m = when (v) {
            "TRUE" -> OKMARK
            "FALSE" -> ERRMARK
            else -> QMARK
        }
        return m
    }

    private fun isRowActive(k: Int, it: TableRow): List<Int> {
        return automaton.getStates(it)
            ?.filter { rs ->
                cex[k, "_${testTable.name}.${rs.name}"] == "TRUE"
            }
            ?.map { it.time }
            ?: listOf()
    }
}