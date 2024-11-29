package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.CliktCommand
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
import com.github.ajalt.clikt.core.main

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