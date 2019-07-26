package edu.kit.iti.formal.automation.testtables.monitor

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton

interface MonitorGeneration {
    val key: String
    fun generate(gtt: GeneralizedTestTable, automaton: TestTableAutomaton): Monitor
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
        var initAtStart: Boolean = true
)

object MonitorFacade {
    val generators = listOf(
            CppMonitorGenerator, CMonitorGenerator,
            MonitorGenerationEsterel, MonitorGenerationST
    )

    fun generateCombinedCpp(name: String, args: List<Pair<GeneralizedTestTable, TestTableAutomaton>>): String {
        val m = CppCombinedMonitorGeneration.generate(name, args);
        return m.preamble + m.body + m.postamble;
    }
}
