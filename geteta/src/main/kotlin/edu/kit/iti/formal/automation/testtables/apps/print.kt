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
package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.Context
import com.github.ajalt.clikt.core.main
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.convert
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.print.HTMLTablePrinter
import edu.kit.iti.formal.automation.testtables.print.LatexTablePrinter
import edu.kit.iti.formal.automation.testtables.print.TextTablePrinter
import edu.kit.iti.formal.util.CodeWriter
import java.io.OutputStreamWriter
import java.util.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (08.08.18)
 */
object Printer {
    @JvmStatic
    fun main(args: Array<String>) = PrinterApp().main(args)
}

class PrinterApp : CliktCommand(name = "ttprint") {
    override fun help(context: Context): String = "generate print files for rtt/gtt "

    enum class Format { HTML, LATEX, TEXT }

    val format by option("-f", "--format")
        .convert { Format.valueOf(it.uppercase(Locale.getDefault())) }
        .default(Format.LATEX)

    val output by option(
        "--output",
        metavar = "FILE",
        help = "Print output to the given file.",
    )
        .file()

    val standalone by option("--standalone", help = "Standalone version (include preamble/postamble)")
        .flag(default = true)

    val file by argument(help = "test table")
        .file(mustExist = true, mustBeReadable = true).multiple()

    override fun run() {
        val gtts = file.flatMap { GetetaFacade.readTables(it) }.map {
            it.ensureProgramRuns()
            it.generateSmvExpression()
            it
        }

        val o = output
        val stream = o?.let { o.bufferedWriter() } ?: OutputStreamWriter(System.out)
        val sink = CodeWriter(stream)

        gtts.forEach { gtt ->
            val printer =
                when (format) {
                    Format.LATEX -> LatexTablePrinter(gtt, sink)
                    Format.HTML -> HTMLTablePrinter(gtt, sink)
                    Format.TEXT -> TextTablePrinter(gtt, sink)
                }

            if (standalone) printer.printPreamble()
            printer.print()
            if (standalone) printer.printPostamble()
            stream.flush()
        }
    }
}
