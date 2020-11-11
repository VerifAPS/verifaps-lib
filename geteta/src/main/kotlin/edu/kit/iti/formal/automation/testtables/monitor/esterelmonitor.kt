package edu.kit.iti.formal.automation.testtables.monitor

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.util.CodeWriter
import java.io.StringWriter

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.09.18)
 */
object MonitorGenerationEsterel : MonitorGeneration {
    override val key = "esterel"
    override fun generate(gtt: GeneralizedTestTable, automaton: TestTableAutomaton, options: MonitorGenerationOptions) =
            Monitor(body = Impl(gtt, automaton).call())

    internal class Impl(private val gtt: GeneralizedTestTable,
                        private val automaton: TestTableAutomaton) {

        var moduleName = "monitor"

        fun call(): String {
            val stream = StringWriter()
            val out = CodeWriter(stream)
            out.write("module $moduleName : ").block {
                out.nl().print("input ")
                gtt.programVariables.joinTo(out, ", ") { it.name }
                out.print(";")

                out.nl().print("signal ")

            }
            return stream.toString()
        }
    }
}