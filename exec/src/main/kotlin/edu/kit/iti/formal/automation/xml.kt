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
package edu.kit.iti.formal.automation

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.main
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration
import edu.kit.iti.formal.automation.st.ast.TypeDeclarations
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.automation.visitors.findFirstProgram
import org.antlr.v4.runtime.CharStreams
import java.io.OutputStreamWriter

object Xml2TxtApp {
    @JvmStatic
    fun main(args: Array<String>) = Xml2Txt().main(args)
}

class Xml2Txt : CliktCommand() {
    val ppu by option("--ppu").flag()

    val input by argument(name = "XML", help = "Files to read").file()

    val simplify by option("--simplify", "-s").flag()

    val noSfc by option("--translate-sfc").flag()

    val noFbd by option("--translate-fbd").flag()

    val preOutput by option("-po", "--pre-output", help = "File to write").file()

    val output by option("-o", "--output", help = "File to write").file()

    override fun run() {
        IEC61131Facade.useOldSfcTranslator = true

        // val base = if (includeBuiltIn) BuiltinLoader.loadDefault() else PouElements()
        val text = IECXMLFacade.extractPLCOpenXml(input)
        val out = output?.bufferedWriter() ?: OutputStreamWriter(System.out)

        if (!noSfc && !noFbd) {
            out.use { out.write(text) }
            return
        }

        preOutput?.writeText(text)

        val pous = IEC61131Facade.file(CharStreams.fromString(text))
        pous.addAll(BuiltinLoader.loadDefault())
        IEC61131Facade.resolveDataTypes(pous)

        if (ppu) {
            pous.findFirstProgram()?.let {
                it.scope.variables.forEach { vd ->
                    if (vd.name.startsWith("Sensor_")) {
                        vd.type = vd.type or VariableDeclaration.INPUT
                    }
                    if (vd.name.startsWith("Actuator_")) {
                        vd.type = VariableDeclaration.OUTPUT
                    }
                }
            }
        }

        if (noSfc) IEC61131Facade.translateSfcToSt(pous)
        if (noFbd) IEC61131Facade.translateFbd(pous)
        if (simplify) {
            IEC61131Facade.resolveDataTypes(pous)
            val p = SymbExFacade.simplify(pous)

            if (ppu) {
                p.findFirstProgram()?.let {
                    it.scope.variables.forEach { vd ->
                        if (vd.name.startsWith("SENSOR_")) {
                            vd.type = VariableDeclaration.INPUT
                        }
                        if (vd.name.startsWith("ACTUATOR_")) {
                            vd.type = VariableDeclaration.OUTPUT
                        }
                    }
                }
            }

            p.forEach {
                if (it is ProgramDeclaration) {
                    IEC61131Facade.printTo(out, it, true)
                }
            }

            pous.forEach {
                if (it is TypeDeclarations && it[0].name != "SFC_STEPS") {
                    IEC61131Facade.printTo(out, it, true)
                }
            }
        } else {
            IEC61131Facade.printTo(out, pous, true)
        }
        out.close()
    }
}