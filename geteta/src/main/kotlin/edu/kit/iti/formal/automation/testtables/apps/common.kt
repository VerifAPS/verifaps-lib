package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.core.ParameterHolder
import com.github.ajalt.clikt.parameters.groups.OptionGroup
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.multiple
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.util.currentDebugLevel
import edu.kit.iti.formal.util.info
import kotlin.system.exitProcess



class CexAnalysationArguments() : OptionGroup() {
    val runAnalyzer by option("--row-map", help = "print out a row mapping")
            .flag("--no-row-map", default = false)

    val odsExport by option("--ods", help = "generate ods counterexample file").file()
    val odsOpen by option("--ods-open").flag()

    val cexPrinter by option("--cexout", help = "prints an analysation of the counter example and the program")
            .flag()

}

class AutomataOptions : OptionGroup() {
    val drawAutomaton by option("--debug-automaton").flag(default = false)
    val showAutomaton by option("--show-automaton").flag(default = false)
}

class TableArguments() : OptionGroup() {
    fun readTables(): List<GeneralizedTestTable> {
        return table.flatMap {
            info("Use table file ${it.absolutePath}")
            GetetaFacade.readTables(it)
        }.map {
            it.ensureProgramRuns()
            it.generateSmvExpression()
            it.simplify()
        }.filterByName(tableWhitelist)

    }

    val table by option("-t", "--table", help = "the xml file of the table", metavar = "FILE")
            .file(exists = true, readable = true)
            .multiple(required = true)
    val tableWhitelist by option("--select-table", metavar = "TABLE_NAME",
            help = "specify tables which should be considered")
            .multiple()
    val enableMesh by option("--meshed").flag("-M", default = false)
}