package edu.kit.iti.formal.automation.testtables.monitor

import edu.kit.iti.formal.automation.cpp.TranslateToCppFacade.dataType
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.automata.RowState
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.automation.testtables.model.automata.Transition
import edu.kit.iti.formal.automation.testtables.model.automata.TransitionType
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.joinInto

/**
 * TODO extrinsic reset
 * @author Alexander Weigl
 * @version 1 (14.07.19)
 */
object CppMonitorGenerator : MonitorGeneration {
    override fun generate(gtt: GeneralizedTestTable, automaton: TestTableAutomaton): String {
        val impl = CppMonitorGeneratorImpl(gtt, automaton)
        return impl.call()
    }
}

class CppMonitorGeneratorImpl(val gtt: GeneralizedTestTable, val automaton: TestTableAutomaton) {
    val cw = CodeWriter()

    val structNameIo = "${gtt.name}_io_t"
    val structNameGv = "${gtt.name}_gv_t"
    val enumStates = "${gtt.name.capitalize()}States"
    val cppRewriter =
            SmvToCTranslator().also {
                gtt.programVariables.forEach { pv ->
                    it.variableReplacement[pv.name] = "input.${pv.name}"
                }
                gtt.constraintVariables.forEach { cv ->
                    it.variableReplacement[cv.name] = "token.globalVars.${cv.name}"
                }
            }

    private fun defineIOStruct() {
        cw.cblock("struct $structNameIo {", "};") {
            gtt.programVariables.forEach { pv ->
                print("${dataType(pv.dataType)}  ${pv.name};")
                        .println("// ${pv.io}")
            }
        }
        cw.nl().nl()
    }

    private fun defineGlobalVarStruct() {
        cw.cblock("struct $structNameGv {", "};") {
            gtt.constraintVariables.forEach { pv ->
                println("${dataType(pv.dataType)}  ${pv.name};")
            }
            gtt.constraintVariables.forEach { pv ->
                println("bool is_bound_${pv.name};")
            }
        }.nl()
        cw.println("const struct $structNameGv ${structNameGv}_default;").nl().nl()
    }

    private fun defineStateEnum() {
        cw.cblock("enum $enumStates {", "};") {
            val states = automaton.getRowStates() +
                    automaton.stateError + automaton.stateSentinel
            val rows = states.joinToString(",") { it.name }
            append(rows)
        }
        cw.nl().nl()
    }

    fun call(): String {
        defineIOStruct()
        defineGlobalVarStruct()
        defineStateEnum()

        cw.cblock(
                "class ${gtt.name.capitalize()}Monitor " +
                        ": public Monitor<$structNameGv,$structNameIo> {", "};") {
            println("public:").nl()
            cblock("void reset() override {", "}") {
                println("Monitor::reset();")
                automaton.getStartStates().forEach {
                    val state = "${enumStates}::${it.name}"
                    println("tokens.push_back((struct Token) { .state = $state, .globalVars = ${structNameGv}_default });")
                }
            }


            cw.nl().cblock("void evaluate (vector<Token> &newTokens, Token &token, const $structNameIo &input) override {",
                    "}") {
                //println("bool newToken = false;")
                cblock("switch(token.state) {", "}") {
                    automaton.rowStates.forEach { (tr, rs) ->
                        rs.forEach { println("case ${enumStates}::${it.name}:") }
                        increaseIndent()
                        nl().print("bool __inputcnstr = ${expr(tr.inputExpr)};")
                        nl().print("bool __outputcnstr  = ${expr(tr.outputExpr)};")

                        nl().cblock("switch(token.state) {", "}") {
                            rs.forEach { generateCase(it) }
                        }
                        decreaseIndent()
                    }
                }
            }
        }
        return cw.stream.toString()
    }

    private fun generateCase(it: RowState) {
        cw.cblock("case ${enumStates}::${it.name}:", "break;") {
            //println("boolean tokenUsed = false;")
            //println("/* */")
            for (t in automaton.getOutgoingTransition(it)) {
                handleTransition(t)
            }
        }
    }

    private fun handleTransition(t: Transition) {
        val condition = when (t.type) {
            TransitionType.ACCEPT -> "__inputcnstr && __outputcnstr"
            TransitionType.ACCEPT_PROGRESS ->
                "__inputcnstr && __outputcnstr"
            TransitionType.FAIL ->
                "__inputcnstr && !__outputcnstr"
            TransitionType.TRUE -> "true"
        }

        cw.nl().cblock("if($condition) {", "}") {
            val to = t.to.name
            println("newTokens.push_back({.state=$enumStates::$to});")
        }
    }

    private fun expr(expr: MutableMap<String, SMVExpr>): String {
        if (expr.isEmpty()) return "true"

        val sb = StringBuilder()
        expr.joinInto(sb, " && ") { _, b ->
            sb.append(b.accept(cppRewriter))
        }
        return sb.toString()
    }

}

