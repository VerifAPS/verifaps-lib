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
import com.github.ajalt.clikt.core.main
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.st.HccPrinter
import edu.kit.iti.formal.automation.st0.trans.SCOPE_SEPARATOR
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.builder.GttMiterConstruction
import edu.kit.iti.formal.automation.testtables.builder.InvocationBasedProductProgramBuilder
import edu.kit.iti.formal.automation.testtables.builder.ProgMiterConstruction
import edu.kit.iti.formal.automation.visitors.findFirstProgram
import edu.kit.iti.formal.util.CodeWriter
import java.io.File

object SMTeta {
    @JvmStatic
    fun main(args: Array<String>) = SMTetaApp().main(args)
}

class SMTetaApp : CliktCommand() {
    val programFile by argument(help = "program file", name = "PROGRAM").file(mustExist = true)
    val tableFile by argument(help = "GTT file", name = "GTT").file(mustExist = true)

    val outputFile by option("--output", "-o", help = "destination to write output files")
        .file()
        .default(File("productProgram.hcc"))

    override fun run() {
        SCOPE_SEPARATOR = "__"
        //region read table
        val gtt = GetetaFacade.readTables(tableFile).first()
        gtt.programRuns = listOf("")
        gtt.generateSmvExpression()
        val gttAsAutomaton = GetetaFacade.constructTable(gtt).automaton
        //endregion

        //region read program
        val progs = IEC61131Facade.fileResolve(programFile).first
        //endregion

        val enum = progs.findFirstProgram()?.scope?.enumValuesToType() ?: mapOf()
        val mc = GttMiterConstruction(gtt, gttAsAutomaton, enum)
        val miter = mc.constructMiter()
        val productProgramBuilder = InvocationBasedProductProgramBuilder()
        val program = ProgMiterConstruction(progs).constructMiter()
        productProgramBuilder.add(program)
        productProgramBuilder.add(miter)
        val productProgram = productProgramBuilder.build(false)
        val out = outputFile.bufferedWriter()
        val simplifiedProductProgram = SymbExFacade.simplify(productProgram)
        val hccprinter = HccPrinter(CodeWriter(out))
        hccprinter.isPrintComments = true
        simplifiedProductProgram.accept(hccprinter)
        out.close()
    }
}
