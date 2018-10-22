package edu.kit.iti.formal.automation.testtables.print

import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.Duration
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.ProgramVariable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.times
import java.io.StringWriter

/**
 *  ```
┌──┬──┐  ╔══╦══╗ ╒══╤══╕ ╓──╥──╖
│  │  │  ║  ║  ║ │  │  │ ║  ║  ║
├──┼──┤  ╠══╬══╣ ╞══╪══╡ ╟──╫──╢
│  │  │  ║  ║  ║ │  │  │ ║  ║  ║
└──┴──┘  ╚══╩══╝ ╘══╧══╛ ╙──╨──╜
 * ```
 * @author Alexander Weigl
 * @version 1 (22.10.18)
 */

data class AsciiBorderCharacters(
        val TOP_LEFT: Char,
        val TOP_MID: Char,
        val TOP_RIGHT: Char,
        val MID_LEFT: Char,
        val MID_MID: Char,
        val MID_RIGHT: Char,
        val BOT_LEFT: Char,
        val BOT_MID: Char,
        val BOT_RIGHT: Char,
        val HORIZONTAL: Char,
        val VERTICAL: Char)

val SINGLE_BORDER = AsciiBorderCharacters('┌',
        '┬', '┐', '├',
        '┼', '┤', '└',
        '┴', '┘', '─', '│')

val DOUBLE_BORDER = AsciiBorderCharacters('╔',
        '╦', '╗', '╠',
        '╬', '╣', '╚',
        '╩', '╝', '═',
        '║')

data class TextPrinterOptions(
        var MIN_WIDTH_COLUMN: Int = 8,
        var DONT_CARE: String = "-",
        var REPEAT_LINES: Boolean = false,
        var REPEAT_REPLACEMENT: String = "",
        var BORDER: AsciiBorderCharacters = SINGLE_BORDER,
        val PADDING: Int = 1 // spaces left and right
        , val MIDDLE_LINES: Boolean = false
) {
}


data class Cell(
        var content: String,
        var spanRows: Int = 1,
        var spanColumns: Int = 1,
        var width: Int = -1
)

class TextTablePrinter(gtt: GeneralizedTestTable,
                       stream: CodeWriter,
                       val options: TextPrinterOptions = TextPrinterOptions()
) : AbstractTablePrinter(gtt, stream) {
    lateinit var grid: Array<Array<Cell>>
    var column = 0

    override fun cellFormatter(c: TestTableLanguageParser.CellContext): String = c.text

    override fun tableBegin() {
        val columns = 1 + input.size + output.size + depth
        val rows = 2 + gtt.region.flat().size
        grid = Array(rows) { Array(columns) { Cell("") } }

        grid[0][0].content = "#"
        grid[0][1].content = "INPUT"
        grid[0][1].spanColumns = input.size
        grid[0][1 + input.size].content = "OUTPUT"
        grid[0][1 + input.size].spanColumns = output.size
        grid[0][1 + input.size + output.size].content = "DURATION"
        grid[0][1 + input.size + output.size].spanColumns = depth

        val variables = (input + output).map { it.name }
        variables.forEachIndexed { i, it ->
            grid[1][1 + i].content = it
        }
    }

    override fun rowBegin() {
        grid[currentRow + 2][0].content = (currentRow).toString()
        column = 1
    }

    override fun printCell(v: ProgramVariable, row: TableRow) {
        val cell = helper.columns[v.name]?.get(currentRow)!!
        grid[currentRow + 2][column++].content = cell.content
    }

    override fun printRowDuration(duration: Duration) {
        grid[currentRow + 2][column++].content = beautifyDuration(duration)
    }

    override fun printGroupDuration(dur: Duration, rowSpan: Int) {
        grid[currentRow + 2][column].spanRows = rowSpan
        grid[currentRow + 2][column++].content = beautifyDuration(dur)
    }

    private fun beautifyDuration(d: Duration): String {
        val stream = StringWriter()
        DSLTablePrinter(CodeWriter(stream)).print(d)
        return stream.toString()
    }

    override fun print() {
        super.print()
        GridPrinter(grid, stream, options)
    }
}

class GridPrinter(
        val grid: Array<Array<Cell>>,
        val stream: CodeWriter,
        val options: TextPrinterOptions) {
    init {
        calculateWidth()
        cleanUpGrid()
        for (row in 0..grid.lastIndex) {
            printRow(row)
        }
        printBorderHB(grid.last())
    }

    private fun printRow(row: Int) {
        val cells = grid[row]

        if (row == 0)
            printBorderHT(grid[row])
        if (row == 1 || row == 2)
            printBorderHM(grid[row])
        if (row > 2 && options.MIDDLE_LINES)
            printBorderHM(grid[row])

        stream.print(options.BORDER.VERTICAL)
        cells.joinTo(stream, options.BORDER.VERTICAL.toString()) {
            String.format(" %-${it.width - 2}s ", it.content)
        }
        stream.print(options.BORDER.VERTICAL)
        stream.nl()
    }

    private fun printBorderHT(cells: Array<Cell>) =
            printBorderH(cells, options.BORDER.TOP_LEFT,
                    options.BORDER.TOP_MID, options.BORDER.TOP_RIGHT,
                    options.BORDER.HORIZONTAL)

    private fun printBorderHM(cells: Array<Cell>) =
            printBorderH(cells, options.BORDER.MID_LEFT,
                    options.BORDER.MID_MID, options.BORDER.MID_RIGHT,
                    options.BORDER.HORIZONTAL)

    private fun printBorderHB(cells: Array<Cell>) =
            printBorderH(cells, options.BORDER.BOT_LEFT,
                    options.BORDER.BOT_MID, options.BORDER.BOT_RIGHT,
                    options.BORDER.HORIZONTAL)


    private fun printBorderH(cells: Array<Cell>,
                             startCorner: Char,
                             midCorner: Char,
                             stopCorner: Char,
                             horizontal: Char) {
        stream.print(startCorner)
        cells.joinTo(stream, midCorner.toString()) { (horizontal.toString() * (it.width)) }
        stream.print(stopCorner)
        stream.nl()
    }

    private fun calculateWidth() {
        //add padding
        val columns = grid[0].size
        for (c in 0 until columns) {
            val cells = grid.map { it[c] }
            val width = cells.asSequence()
                    .map { options.PADDING * 2 + if (it.width < 0) it.content.length else it.width }
                    .max() ?: options.MIN_WIDTH_COLUMN
            cells.forEach { it.width = Math.max(options.MIN_WIDTH_COLUMN, width) }
        }
    }


    private fun cleanUpGrid() {
        grid.forEachIndexed { rowIdx, row ->
            val seq = Array<Cell>(row.size) { row[it].copy() }

            var idx = 0
            while (idx < row.size) {
                var cell = seq[idx]
                if (cell.spanColumns > 1) {
                    val consumed = seq.slice(idx + 1 until idx + cell.spanColumns)
                    val w = consumed.sumBy { it.width +  options.PADDING }
                    cell.width += w
                    consumed.forEach { it.width = 0 }
                    idx += cell.spanColumns;
                    continue
                }
                idx++;
                continue
            }
            grid[rowIdx] = seq.filter { it.width > 0 }.toTypedArray()
        }
    }
}
