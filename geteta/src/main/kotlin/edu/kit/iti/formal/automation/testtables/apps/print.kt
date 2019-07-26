package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
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

/**
 *
 * @author Alexander Weigl
 * @version 1 (08.08.18)
 */
object Printer {
    @JvmStatic
    fun main(args: Array<String>) = PrinterApp().main(args)
}

class PrinterApp : CliktCommand() {
    enum class Format { HTML, LATEX, TEXT }

    val format by option("-f", "--format")
            .convert { Format.valueOf(it.toUpperCase()) }
            .default(Format.LATEX)

    val output by option("--output",
            metavar = "FILE",
            help = "Print output to the given file.")
            .file()

    val standalone by option("--standalone", help = "Standalone version (include preamble/postamble)")
            .flag(default = true)

    val file by argument(help = "test table")
            .file(exists = true, readable = true)

    override fun run() {
        val gtt = GetetaFacade.readTable(file)

        val o = output
        val stream = o?.let { o.bufferedWriter() } ?: OutputStreamWriter(System.out)
        val sink = CodeWriter(stream)

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

