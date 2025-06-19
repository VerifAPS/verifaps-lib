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
package edu.kit.iti.formal.automation.testtables.print

import edu.kit.iti.formal.automation.testtables.grammar.*
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.center
import edu.kit.iti.formal.util.times
import java.io.StringWriter
import javax.swing.SwingConstants
import kotlin.math.max

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

/**
 * Class holds the characters for drawing the borders.
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
    val VERTICAL: Char,
)

/**
 * Single frame borders:
 * ```
┌──┬──┐
│  │  │
├──┼──┤
│  │  │
└──┴──┘
 * ```
 * @author Alexander Weigl
 * @version 1 (22.10.18)
 */
val SINGLE_BORDER = AsciiBorderCharacters(
    '┌',
    '┬', '┐', '├',
    '┼', '┤', '└',
    '┴', '┘', '─', '│',
)

/**
 * Double frame borders:
 *  ```
╔══╦══╗
║  ║  ║
╠══╬══╣
║  ║  ║
╚══╩══╝
 * ```
 * @author Alexander Weigl
 * @version 1 (22.10.18)
 */
val DOUBLE_BORDER = AsciiBorderCharacters(
    '╔',
    '╦', '╗', '╠',
    '╬', '╣', '╚',
    '╩', '╝', '═',
    '║',
)

/**
 * Options for Text printing.
 */
data class TextPrinterOptions(
    var columnMinWidth: Int = 8,
    var dontCareChar: String = "-",
    var printEmptyCells: Boolean = false,
    var emptyCellReplacement: String = "",
    var border: AsciiBorderCharacters = SINGLE_BORDER,
    // spaces left and right
    val spacePadding: Int = 1,
    val drawLinesBetweenRows: Boolean = false,
)

/**
 * Represents a text cell
 */
data class Cell(
    var content: String,
    var spanRows: Int = 1,
    var spanColumns: Int = 1,
    /**
     * -1 for unset width, 0 for removal, otherwise contains width in characters
     */
    var width: Int = -1,
    /**
     * Orientation of the cell.
     * One of [SwingConstants.LEFT], [SwingConstants.CENTER] or
     * [SwingConstants.RIGHT]
     */
    var orientation: Int = SwingConstants.LEFT,
)

class TextTablePrinter(
    gtt: GeneralizedTestTable,
    stream: CodeWriter,
    val options: TextPrinterOptions = TextPrinterOptions(),
) : AbstractTablePrinter(gtt, stream) {
    lateinit var grid: Array<Array<Cell>>
    var column = 0

    init {
        init()
    }

    override fun cellFormatter(c: TestTableLanguageParser.CellContext): String = c.text

    override fun tableBegin() {
        val columns = 1 + input.size + output.size + depth
        val rows = 2 + gtt.region.flat().size
        grid = Array(rows) { Array(columns) { Cell("") } }

        grid[0][0].content = "#"
        grid[0][0].orientation = SwingConstants.CENTER

        grid[0][1].content = "INPUT"
        grid[0][1].spanColumns = input.size
        grid[0][1].orientation = SwingConstants.CENTER

        grid[0][1 + input.size].content = "OUTPUT"
        grid[0][1 + input.size].spanColumns = output.size
        grid[0][1 + input.size].orientation = SwingConstants.CENTER

        grid[0][1 + input.size + output.size].content = "DURATION"
        grid[0][1 + input.size + output.size].spanColumns = depth
        grid[0][1 + input.size + output.size].orientation = SwingConstants.CENTER

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

class GridPrinter(val grid: Array<Array<Cell>>, val stream: CodeWriter, val options: TextPrinterOptions) {
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

        if (row == 0) {
            printBorderHT(grid[row])
        }
        if (row == 1 || row == 2) {
            printBorderHM(grid[row])
        }
        if (row > 2 && options.drawLinesBetweenRows) {
            printBorderHM(grid[row])
        }

        stream.print(options.border.VERTICAL)
        cells.joinTo(stream, options.border.VERTICAL.toString()) {
            when (it.orientation) {
                SwingConstants.LEFT ->
                    String.format(" %${it.width - 2}s ", it.content)

                SwingConstants.CENTER ->
                    it.content.center(it.width)

                SwingConstants.RIGHT ->
                    String.format(" %-${it.width - 2}s ", it.content)

                else -> throw IllegalStateException("Illegal orientation supplied")
            }
        }
        stream.print(options.border.VERTICAL)
        stream.nl()
    }

    private fun printBorderHT(cells: Array<Cell>) = printBorderH(
        cells,
        options.border.TOP_LEFT,
        options.border.TOP_MID,
        options.border.TOP_RIGHT,
        options.border.HORIZONTAL,
    )

    private fun printBorderHM(cells: Array<Cell>) = printBorderH(
        cells,
        options.border.MID_LEFT,
        options.border.MID_MID,
        options.border.MID_RIGHT,
        options.border.HORIZONTAL,
    )

    private fun printBorderHB(cells: Array<Cell>) = printBorderH(
        cells,
        options.border.BOT_LEFT,
        options.border.BOT_MID,
        options.border.BOT_RIGHT,
        options.border.HORIZONTAL,
    )

    private fun printBorderH(
        cells: Array<Cell>,
        startCorner: Char,
        midCorner: Char,
        stopCorner: Char,
        horizontal: Char,
    ) {
        stream.print(startCorner)
        cells.joinTo(stream, midCorner.toString()) { (horizontal.toString() * (it.width)) }
        stream.print(stopCorner)
        stream.nl()
    }

    private fun calculateWidth() {
        // add padding
        val columns = grid[0].size
        for (c in 0 until columns) {
            val cells = grid.map { it[c] }
            val width = cells.asSequence()
                .map { options.spacePadding * 2 + if (it.width < 0) it.content.length else it.width }
                .maxOrNull() ?: options.columnMinWidth
            cells.forEach { it.width = max(options.columnMinWidth, width) }
        }
    }

    private fun cleanUpGrid() {
        grid.forEachIndexed { rowIdx, row ->
            val seq = Array<Cell>(row.size) { row[it].copy() }

            var idx = 0
            while (idx < row.size) {
                val cell = seq[idx]
                if (cell.spanColumns > 1) {
                    val consumed = seq.slice(idx + 1 until idx + cell.spanColumns)
                    val w = consumed.sumOf { it.width + options.spacePadding }
                    cell.width += w
                    consumed.forEach { it.width = 0 }
                    idx += cell.spanColumns
                    continue
                }
                idx++
                continue
            }
            grid[rowIdx] = seq.filter { it.width > 0 }.toTypedArray()
        }
    }
}