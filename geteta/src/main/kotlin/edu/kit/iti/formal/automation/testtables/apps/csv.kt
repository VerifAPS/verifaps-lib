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
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import com.github.doyaaaaaken.kotlincsv.client.CsvReader
import com.github.doyaaaaaken.kotlincsv.dsl.context.CsvReaderContext
import edu.kit.iti.formal.util.CodeWriter
import java.io.File
import java.io.Writer

private const val NOT_FOUND = "/* not given */"
private const val DURATION_COLUMN = "DURATION"

object Csv {
    @JvmStatic
    fun main(args: Array<String>) = CsvApp().main(args)
}

class CsvApp : CliktCommand(name = "ttcsv") {
    override fun helpEpilog(context: Context) = "ttcsv -- Generate table template from csv files."

    private val outputFile by option("-o", help = "output table file", metavar = "FILE")
        .file()
        .default(File("out.tt"))

    private val inputFiles by argument("FILE", help = "CSV files")
        .file(mustExist = true, mustBeReadable = true).multiple()
    private val quoteChar by option("-q").default("\"")
    private val delimChar by option("-d").default(",")

    override fun run() {
        outputFile.bufferedWriter().use { out ->
            val t = CsvTranslator(out, quoteChar, delimChar)
            inputFiles.forEach {
                t.run(it.nameWithoutExtension, it.readText())
            }
        }
    }
}

class CsvTranslator(val writer: Writer, val quoteChar: String, val delimChar: String) {

    fun run(name: String, content: String) {
        val cw = CodeWriter(writer)
        translateCsvFile(cw, name, parseCsv(content))
    }

    private fun parseCsv(input: String) = CsvReaderContext().run {
        this.delimiter = delimChar.first()
        this.quoteChar = this@CsvTranslator.quoteChar.first()
        CsvReader(this).readAllWithHeader(input)
    }

    private val headPattern = "\\s*(?<direction>(in|out|pre|post))?\\s*(?<name>\\w*)\\s*:\\s*(?<dt>\\w*)\\s*".toRegex()

    private fun translateCsvFile(out: CodeWriter, input: String, fields: List<Map<String, String>>) {
        val keys = fields.first().keys
        val varName = HashMap<String, String>()

        require(DURATION_COLUMN in keys) {
            "No duration column given"
        }

        out.cblock("table $input {", "}") {
            keys.forEach {
                if (it == DURATION_COLUMN) {
                    // skip
                } else {
                    val m = headPattern.matchEntire(it)

                    require(m != null) {
                        "Column $it does not match the pattern for program variable headers."
                    }

                    val mods = m.groups["direction"]?.value ?: NOT_FOUND
                    val name = m.groups["name"]?.value ?: NOT_FOUND
                    val dt = m.groups["dt"]?.value ?: NOT_FOUND

                    val modifier = when (mods) {
                        "in" -> "input"
                        "out" -> "output"
                        "pre" -> "state assume"
                        "post" -> "state next assert"
                        else -> ""
                    }

                    nl().print("var $modifier $name : $dt")
                    varName[it] = name
                }
            }
            nl()

            out.cblock("group {", "}") {
                fields.forEach { row ->
                    val duration = row[DURATION_COLUMN] ?: "[1,1]" // default value
                    cblock("row $duration {", "}") {
                        row.forEach { (k, v) ->
                            if (k != DURATION_COLUMN) {
                                nl().print("${varName[k]}: $v")
                            }
                        }
                    }
                    nl()
                }
            }
        }
    }
}