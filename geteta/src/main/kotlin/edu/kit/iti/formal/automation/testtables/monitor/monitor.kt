package edu.kit.iti.formal.automation.testtables.monitor

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton

data class MonitorGenerationOptions(
        val includes : List<String> = listOf()
)

interface MonitorGeneration {
    val key: String
    fun generate(gtt: GeneralizedTestTable, automaton: TestTableAutomaton,
                 options : MonitorGenerationOptions = MonitorGenerationOptions()): Monitor
}

interface CombinedMonitorGeneration {
    val key: String
    fun generate(
            name : String,
            input: List<Pair<GeneralizedTestTable, TestTableAutomaton>>): Monitor
}

data class Monitor(
        var name: String = "",
        var body: String = "",
        var types: String = "",
        var preamble: String = "",
        var postamble: String = "",
        var static: Boolean = true
)
