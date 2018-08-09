package edu.kit.iti.formal.automation.testtables.print

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.ProgramVariable
import java.util.*
import kotlin.collections.set

/**
 *
 * @author Alexander Weigl
 * @version 1 (07.08.18)
 */
interface TablePrinter {
    fun printPreamble()
    fun print()
    fun printPostamble()
}

data class PrintCellContent(
        var content: String = "",
        var groupDuration: Int = 0,
        var originalEmpty: Boolean = false,
        var endGroup: Boolean = false
) {
    val beginGroup: Boolean
        get() = groupDuration == 0
    val singleGroup: Boolean
        get() = endGroup && secondInGroup
    val secondInGroup: Boolean
        get() = groupDuration == 1
    val inBetween: Boolean
        get() = !beginGroup && !endGroup
}
typealias CellPrinter = (TestTableLanguageParser.CellContext) -> String

class PrinterHelper(gtt: GeneralizedTestTable,
                    val cellPrinter: CellPrinter
) {
    val states = gtt.region.flat()
    val columns = LinkedHashMap<String, List<PrintCellContent>>()

    init {
        gtt.programVariables.forEach { columns[it.name] = calculateColumn(it) }
    }

    fun calculateColumn(column: ProgramVariable): List<PrintCellContent> {
        var previousContent = GetetaFacade.parseCell("-")
        val seq = states.map { PrintCellContent() }
        var currentGroupDuration = 0

        for (i in 0 until seq.size) {
            val v = states[i].rawFields[column]
            val c = seq[i]

            if (v != null) {
                previousContent = v
                c.content = cellPrinter(v)
                c.groupDuration = 0
                currentGroupDuration = 0
                if (i != 0) {
                    seq[i - 1].endGroup = true
                }
            } else {
                c.originalEmpty = true
                c.content = cellPrinter(previousContent)
                c.groupDuration = ++currentGroupDuration
            }
        }
        return seq
    }
}

class Counter {
    private val counter = LinkedHashMap<String, Int>()

    fun peek(s: String): Int =
            counter.computeIfAbsent(s) { _ -> 0 }

    fun getAndIncrement(s: String): Int {
        val peek = peek(s)
        counter[s] = peek + 1
        return peek
    }
}
