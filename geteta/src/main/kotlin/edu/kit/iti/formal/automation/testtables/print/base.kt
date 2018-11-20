package edu.kit.iti.formal.automation.testtables.print

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.util.CodeWriter
import java.util.*
import kotlin.collections.set

/**
 * @author Alexander Weigl
 * @version 1 (07.08.18)
 */

/**
 *
 */
interface TablePrinter {
    /**
     * Prints header information needed for standalone documents.
     * TeX-preamble or html head
     */
    fun printPreamble()

    /**
     * Prints only the table.
     */
    fun print()

    /**
     * Closing statements for the standalone document.
     */
    fun printPostamble()
}

/**
 * PrintCellContent holds printing information about table cells.
 */
data class PrintCellContent(
        /** Content to be displayed */
        var content: String = "",
        /** position in a down streaming group */
        var groupPosition: Int = 0,
        /** signals if the cell was empty and only filled by "down streaming" */
        var originalEmpty: Boolean = false,
        /** signals if the cell is the end of a "down streaming" */
        var endGroup: Boolean = false
) {
    val beginGroup: Boolean
        get() = groupPosition == 0
    val singleGroup: Boolean
        get() = endGroup && secondInGroup
    val secondInGroup: Boolean
        get() = groupPosition == 1
    val inBetween: Boolean
        get() = !beginGroup && !endGroup
}

/**
 * A serializer for table cells.
 */
typealias CellPrinter = (TestTableLanguageParser.CellContext) -> String

/**
 * This class helps printer with serialization of the table cell contents.
 */
class PrinterHelper(gtt: GeneralizedTestTable,
                    val cellPrinter: CellPrinter) {
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
                c.groupPosition = 0
                currentGroupDuration = 0
                if (i != 0) {
                    seq[i - 1].endGroup = true
                }
            } else {
                c.originalEmpty = true
                c.content = cellPrinter(previousContent)
                c.groupPosition = ++currentGroupDuration
            }
        }
        return seq
    }
}

/**
 * [Counter] offers a multiple counters identified by a string
 */
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

/**
 * Base class for TablePrinter.
 *
 * This class provides visitor functions that get called during table visialization.
 */
abstract class AbstractTablePrinter(protected val gtt: GeneralizedTestTable,
                                    protected val stream: CodeWriter) : TablePrinter {

    protected var helper: PrinterHelper
    protected var currentRow = 0
    val input = gtt.programVariables.filter { it.isInput }
    val output = gtt.programVariables.filter { it.isOutput }
    val durations = Stack<Pair<Duration, Int>>()
    val depth = gtt.region.depth()

    init {
        helper = PrinterHelper(gtt, this::cellFormatter)
    }


    override fun printPreamble() {}
    override fun printPostamble() {}

    protected open fun contentBegin() {}
    protected open fun tableBegin() {}
    protected open fun tableEnd() {}
    protected open fun contentEnd() {}
    protected open fun regionEnd() {}
    protected open fun regionBegin() {}
    protected open fun rowBegin() {}
    protected open fun rowEnd() {}

    protected open fun printGroupDuration(dur: Duration, rowSpan: Int) {}
    protected open fun printCell(v: ProgramVariable, row: TableRow) {}
    protected open fun printRowDuration(duration: Duration) {}

    override fun print() {
        contentBegin()
        tableBegin()
        printRegion(gtt.region.children)
        tableEnd()
        contentEnd()
    }

    private fun printRegion(region: List<TableNode>) {
        region.forEach { o ->
            when (o) {
                is TableRow -> printStep(o)
                is Region -> {
                    regionBegin()
                    printRegion(o)
                    regionEnd()
                }
            }
        }
    }

    private fun printRegion(b: Region) {
        durations.push(b.duration to b.count())
        printRegion(b.children)
    }

    private fun printStep(s: TableRow) {
        rowBegin()
        input.forEach { v -> printCell(v, s) }
        output.forEach { v -> printCell(v, s) }

        printRowDuration(s.duration)
        while (!durations.empty()) {
            val (dur, rowSpan) = durations.pop()
            printGroupDuration(dur, rowSpan)
        }
        rowEnd()
        currentRow++
    }

    abstract fun cellFormatter(c: TestTableLanguageParser.CellContext): String
}
