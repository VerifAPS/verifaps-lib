package edu.kit.iti.formal.automation.testtables.apps

import com.github.ajalt.clikt.parameters.groups.OptionGroup
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.util.info


class CexAnalysationArguments() : OptionGroup() {
    val cexJson by option("--cexjson", help = "exports an analysis of the counter example in json").flag()

    val runAnalyzer by option("--row-map", help = "print out a mapping between table rows and states")
            .flag("--no-row-map", default = false)

    val odsExport by option("--ods", help = "generate ods counter-example file").file()
    val odsOpen by option("--ods-open").flag()

    val cexPrinter by option("--cexout", help = "prints an analyis of the counter example and the program")
            .flag()

}

class AutomataOptions : OptionGroup() {
    val drawAutomaton by option("--debug-automaton", help="generate a dot file, showing the generated automaton").flag(default = false)
    val showAutomaton by option("--show-automaton", help="run dot and show the image of the automaton").flag(default = false)
}

class TableArguments() : OptionGroup() {
    fun readTables(): List<GeneralizedTestTable> {
        return table.flatMap {
            info("Use table file ${it.absolutePath}")
            info("Time constants: $timeConstants")
            GetetaFacade.readTables(it, timeConstants)
        }.map {
            it.ensureProgramRuns()
            it.generateSmvExpression()
            it.simplify()
        }.filterByName(tableWhitelist)

    }

    val timeConstants: Map<String, Int> by option("-T", help = "setting a time constant")
            .splitPair("=")
            .convert{ it.first to it.second.toInt()}
            .multiple()
            .toMap()

    val table by option("-t", "--table", help = "test table file", metavar = "FILE")
            .file(mustExist = true, mustBeReadable = true)
            .multiple(required = true)
    val tableWhitelist by option("--select-table", metavar = "TABLE_NAME",
            help = "specify table by name, which should be used from the given file")
            .multiple()
    val enableMesh by option("--meshed", help="enable experimental meshed tables")
            .flag("-M", default = false)
}