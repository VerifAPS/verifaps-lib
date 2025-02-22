package edu.kit.iti.formal.automation.testtables.viz

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.smv.CounterExample
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.ast.SVariable
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.times

class CounterExampleTablePrinter(
    val automaton: TestTableAutomaton,
    val testTable: GeneralizedTestTable,
    val cex: CounterExample,
    val stream: CodeWriter = CodeWriter()
) {

    fun print() {
        for (k in 0 until cex.stateSize - 1) get(k)
    }

    fun get(k: Int) {
        printAssertions(k)
    }

    private fun printAssertions(k: Int) {
        val stars = ("*" * 79)
        stream.print("($stars").nl()
        stream.print(" * Table rows:").nl()
        printVariables(k)
        stream.nl().println("$stars)")
    }

    private fun printVariables(k: Int) {
        for (row in testTable.region.flat()) {
            val activateStates = isRowActive(k, row)
            val rowActive = if (activateStates.isNotEmpty()) OKMARK else ERRMARK
            val prfx = "_${testTable.name}."
            val assumption = prfx + row.defInput.name
            val assertion = prfx + row.defOutput.name
            val fwd = prfx + row.defForward.name

            val times = activateStates.joinToString(", ") { it.toString() }

            stream.print(" *     $rowActive Row ${row.id} " +
                    "${boolForHuman(k, assumption)} --> ${boolForHuman(k, assertion)}:" +
                    " ${boolForHuman(k, fwd)} (Time: $times)").nl()

            if (activateStates.isNotEmpty() && !bool(k, assumption)) {
                val violatedAssumpations = testTable.programVariables.filter { it.isAssumption }
                    .map {
                        SVariable(row.defInput.name + "_" + it.name, SMVTypes.BOOLEAN)
                    }
                    .filter { !bool(k, it.name) }
                    .joinToString { it.name }
                stream.print(" *         Violated assumptions: $violatedAssumpations").nl()
            }

            if (activateStates.isNotEmpty() && !bool(k, assertion)) {
                val violatedAssertions = testTable.programVariables.filter { it.isAssertion }
                    .map {
                        prfx + row.defOutput.name + "_" + it.internalVariable(testTable.programRuns).name
                    }
                    .filter { !bool(k, it) }
                    .joinToString { it }
                stream.print(" *         Violated assertions: $violatedAssertions").nl()
            }
        }
    }

    private fun bool(k: Int, n: String) = when (cex[k, n]) {
        "TRUE" -> true
        "FALSE" -> false
        else -> false
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