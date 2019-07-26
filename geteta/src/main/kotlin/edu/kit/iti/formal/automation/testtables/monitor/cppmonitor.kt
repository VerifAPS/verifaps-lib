package edu.kit.iti.formal.automation.testtables.monitor

import edu.kit.iti.formal.automation.cpp.TranslateToCppFacade.dataType
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.ProgramVariable
import edu.kit.iti.formal.automation.testtables.model.automata.RowState
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.automation.testtables.model.automata.Transition
import edu.kit.iti.formal.automation.testtables.model.automata.TransitionType
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.joinInto

val EMPTY_COLUMN = SVariable("ERROR", SMVTypes.BOOLEAN);
val CPP_PREAMBLE by lazy {
    CppMonitorGenerator.javaClass.getResourceAsStream("monitors/preamble.hpp").use {
        it.bufferedReader().readText()
    }
}

val CPP_POSTAMBLE = ""


/**
 * TODO extrinsic reset
 * @author Alexander Weigl
 * @version 1 (14.07.19)
 */
object CppMonitorGenerator : MonitorGeneration {
    override val key: String = "cpp"
    override fun generate(gtt: GeneralizedTestTable, automaton: TestTableAutomaton): Monitor {
        val impl = CppMonitorGeneratorImpl(gtt, automaton)
        return impl.call()
    }
}

class CppMonitorGeneratorImpl(val gtt: GeneralizedTestTable, val automaton: TestTableAutomaton) {
    val monitor = Monitor(gtt.name, "", "")
    val cw = CodeWriter()

    val structNameIo = "${gtt.name}_io_t"
    val structNameGv = "gv_t"
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

    fun call(): Monitor {
        defineIOStruct(structNameIo, gtt.programVariables)

        cw.println("template <typename io_t>")
                .cblock("class ${gtt.name.capitalize()}Monitor " +
                        ": public BaseMonitor<io_t> {", "};") {
                    defineGlobalVarStruct()
                    defineStateEnum()
                    println("public:").nl()
                    cblock("void reset() override {", "}") {
                        println("BaseMonitor::reset();")
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
        monitor.body = cw.stream.toString()
        return monitor
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

object CppCombinedMonitorGeneration : CombinedMonitorGeneration {
    override fun generate(name: String, input: List<Pair<GeneralizedTestTable, TestTableAutomaton>>): Monitor {
        return CppCombinedMonitorGenerationImpl(name, input).call()
    }

    override val key = "cpp"
}

class CppCombinedMonitorGenerationImpl(val name: String,
                                       val input: List<Pair<GeneralizedTestTable, TestTableAutomaton>>) {
    private val base: MonitorGeneration = CppMonitorGenerator
    private val containsDynamic = input.any { (a, b) -> a.options.monitor.dynamic }
    private val subMonitors = input.map { (a, b) -> base.generate(a, b) }
    private val monitor = Monitor()

    fun call(): Monitor {
        generate(); return monitor
    }

    private fun generate() {
        inputStruct()
        val ownBody = getOwnBody()
        monitor.body = subMonitors.joinToString("\n\n") { it.body } + ownBody
        monitor.preamble = CPP_PREAMBLE
        monitor.postamble = CPP_POSTAMBLE
    }

    private fun inputStruct() {
        val combinedVariables =
                input.map { (gtt, _) -> gtt.programVariables }
                        .reduce { acc, list ->
                            list.forEach { pv ->
                                val collision = acc.find { it.name == pv.name }
                                if (collision != null && collision.dataType != pv.dataType)
                                    throw IllegalStateException("Datatype clash for variable: ${pv.name}")
                                if (collision == null) acc.add(pv)
                            }
                            acc
                        }
        monitor.types += defineIOStruct("${name}_io_t", combinedVariables)
    }

    private fun getOwnBody(): String {
        val ownBody = CodeWriter()
        ownBody.cblock("class $name : CombinedMonitor<io_t> {", "};") {
            if (containsDynamic)
                println("vector<IMonitor<io_t> &> monitors;")

            println("public:")
            val startMon = subMonitors.filter { it.initAtStart }.map { it.name }
            startMon.forEach { println("$it ${it.toLowerCase()};") }

            val init = startMon.joinToString(", ") { "${it.toLowerCase()}()" }
            cblock("$name() : $init  {", "}") { }
            ownBody.cblock("void eval(const io_t &&input) {", "}") {
                startMon.forEach {
                    val n = it.toLowerCase()
                    println("$n.next(input); combine(${n}.state());")
                }
                if (containsDynamic)
                    println("for(auto& m: monitors) {m.next(input); combine(m.state());}")
            }

            if (containsDynamic) {
                cblock("void before(const io_t &&input) {", "}") {
                    input.forEachIndexed { index, (a, b) ->
                        if (a.options.monitor.dynamic) {
                            val m = subMonitors[index]

                            val trigger = a.options.monitor.trigger?.let {
                                GetetaFacade.exprToSMV(it, EMPTY_COLUMN, 0, a.parseContext)
                            } ?: "false"

                            cblock("if($trigger) {", "}") {
                                println("monitors.push_back(${m.name}());")
                            }
                        }
                    }
                }
                cblock("void cleanUpMonitors(const io_t &&input) {", "}") {
                    println("""
auto i = std::begin(monitors);
while (i != std::end(monitors)) {
    if (i.state() == MonitorState::UNKNOWN)
        i = inv.erase(i);
    else
        ++i;
}""".trimIndent())
                }
            }
        }
        return ownBody.stream.toString()
    }
}


private fun defineIOStruct(typeName: String, variables: MutableList<ProgramVariable>): String {
    val cw = CodeWriter()
    cw.cblock("struct $typeName {", "};") {
        variables.forEach { pv ->
            print("${dataType(pv.dataType)}  ${pv.name};")
                    .println("// ${pv.io}")
        }
    }
    cw.nl().nl()
    return cw.toString()
}
