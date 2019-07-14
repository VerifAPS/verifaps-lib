package edu.kit.iti.formal.automation.testtables.monitor

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton

interface MonitorGeneration {
    val getPreamble: String get() = ""
    val getPostamble: String get() = ""
    fun generate(gtt: GeneralizedTestTable, automaton: TestTableAutomaton): String
}

interface CombinedMonitorGeneration {
    fun generate(input: List<Pair<GeneralizedTestTable, TestTableAutomaton>>): String

}

object MonitorFacade {
    val generators = listOf(
            CppMonitorGenerator, CMonitorGenerator,
            MonitorGenerationEsterel, MonitorGenerationST
    )
}
