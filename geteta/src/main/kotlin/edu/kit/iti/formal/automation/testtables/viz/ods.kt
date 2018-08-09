package edu.kit.iti.formal.automation.testtables.viz

import com.github.jferard.fastods.OdsFactory
import com.github.jferard.fastods.Table
import com.github.jferard.fastods.style.BorderAttribute
import com.github.jferard.fastods.style.TableCellStyle
import com.github.jferard.fastods.util.SimpleLength
import edu.kit.iti.formal.automation.sfclang.getUniqueName
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.smv.CounterExample
import java.util.*
import java.util.logging.Logger

class ODSTableWriter constructor(
        private val counterExample: CounterExample,
        private val gtt: GeneralizedTestTable,
        private val mapping: Collection<Mapping>
) : Runnable {
    val odsFactory = OdsFactory.create(Logger.getLogger("example"), Locale.US)
    val writer = odsFactory.createWriter()
    val document = writer.document()

    lateinit var currentTable: Table

    val EMPTY = TableCellStyle.DEFAULT_CELL_STYLE
    val styleRowId: TableCellStyle = EMPTY
    val stylePauseVariableHeader: TableCellStyle = EMPTY

    val styleValues = TableCellStyle.builder("values").build()
    val styleOutputValue = TableCellStyle.builder("values output")
            .parentCellStyle(styleValues).build()
    val styleInputValue = TableCellStyle.builder("values input")
            .parentCellStyle(styleValues).build()

    var styleCategoryHeader = TableCellStyle.builder("category header")
            .backgroundColor("#ff00ff")
            .fontWeightBold()
            .textAlign(TableCellStyle.Align.CENTER)
            .build()

    var styleVariableHeader = TableCellStyle.builder("variable header")
            .backgroundColor("#cccccc")
            .fontWeightBold()
            .textAlign(TableCellStyle.Align.CENTER)
            .borderBottom(SimpleLength.pt(1.0), "#000000", BorderAttribute.Style.SOLID)
            .build()

    val styleInputVariableHeader: TableCellStyle = TableCellStyle.builder("variable input header")
            .parentCellStyle(styleVariableHeader)
            .build()

    val styleOutputVariableHeader = TableCellStyle.builder("variable output header")
            .parentCellStyle(styleVariableHeader)
            .build()

    val styleRowIdHeader: TableCellStyle = TableCellStyle.builder("variable rowid header")
            .parentCellStyle(styleVariableHeader)
            .build()

    val styleRowTimeHeader: TableCellStyle = TableCellStyle.builder("variable time header")
            .parentCellStyle(styleVariableHeader)
            .build()


    override fun run() {
        mapping.forEach { createTable(it) }
    }


    val input = gtt.programVariables.filter { it.isInput }
    val output = gtt.programVariables.filter { it.isOutput }

    private fun createTable(m: Mapping) {
        currentTable = document.addTable(getUniqueName())
        writeHeader()
        writeCounterExample(m)
    }

    private fun writeHeader() {
        writeCategories()
        writeVariableColumns()
    }

    private fun writeCategories() {
        val row = currentTable.nextRow()
        val cell = row.walker

        cell.setStringValue("#")
        cell.setStyle(styleRowIdHeader)
        cell.next()

        if (gtt.options.relational) {
            //TODO
            cell.setStringValue("PAUSE")
            cell.setStyle(styleCategoryHeader)
            cell.setColumnsSpanned(gtt.maxProgramRun)
            cell.next()
        }

        cell.setStringValue("INPUT")
        cell.setStyle(styleCategoryHeader)
        cell.setColumnsSpanned(input.size)
        cell.next()

        cell.setStringValue("OUTPUT")
        cell.setStyle(styleCategoryHeader)
        cell.setColumnsSpanned(output.size)
        cell.next()
    }

    private fun writeVariableColumns() {
        val row = currentTable.nextRow()
        val cell = row.walker

        cell.setStringValue("")
        cell.next()

        if (gtt.options.relational) {
            gtt.programRuns.forEach {
                cell.setStringValue(it)
                cell.setStyle(stylePauseVariableHeader)
                cell.next()
            }
        }


        if (input.isEmpty()) {
            cell.setStringValue("")
            cell.next()
        } else {
            input.forEach {
                cell.setStringValue(it.name)
                cell.setStyle(styleInputVariableHeader)
                cell.next()
            }
        }
        output.forEach {
            cell.setStringValue(it.name)
            cell.setStyle(styleOutputVariableHeader)
            cell.next()
        }
    }

    fun writeCounterExample(map: Mapping) {
        val rowIds = map.asRowList()
        rowIds.forEachIndexed { index, rowId ->
            writeLine(index, rowId)
        }
    }

    private fun writeLine(index: Int, rowId: String) {
        val row = currentTable.nextRow()
        val cell = row.walker

        val tableRow = gtt.getTableRow(rowId)

        cell.setStringValue(tableRow?.id)
        cell.setStyle(styleRowId)
        cell.next()

        if (gtt.options.relational) {
            gtt.programRuns.forEach {
                cell.setStringValue(it)
                cell.setStyle(stylePauseVariableHeader)
                cell.next()
            }
        }

        if (input.isEmpty()) {
            cell.setStringValue("")
            cell.next()
        } else {
            input.forEach {
                //Fix input clashes
                val v = counterExample[index, it.name]
                cell.setStyle(styleInputValue)
                cell.setStringValue(v)
                cell.setTooltip(tableRow?.rawFields?.get(it)?.text)
                cell.next()
            }
        }
        output.forEach {
            val v = counterExample[index, it.externalVariable(gtt.programRuns).name]
            cell.setStyle(styleOutputValue)
            cell.setTooltip(tableRow?.rawFields?.get(it)?.text)
            cell.setStringValue(v)
            cell.next()
        }
    }
}
