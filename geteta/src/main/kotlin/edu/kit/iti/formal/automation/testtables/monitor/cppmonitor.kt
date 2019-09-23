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
                    val name = pv.externalVariable(gtt.programRuns, gtt.name).name
                    it.variableReplacement[name] = "input.${pv.name}"
                }
                gtt.constraintVariables.forEach { cv ->
                    val name = cv.externalVariable(gtt.programRuns, gtt.name).name
                    it.variableReplacement[name] = "token.globalVars.${cv.name}"
                }

                it.rewritingFunction = {it -> it.replace("code$", "input.")}
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
        cw.println("#include \"../mon.h\"")
        defineIOStruct(structNameIo, gtt.programVariables)

        defineGlobalVarStruct()
        defineStateEnum()

        cw.println("template <typename io_t>")
                .cblock("class ${gtt.name.capitalize()}Monitor " +
                        ": public IMonitor<io_t> {", "};") {
                    println("struct Token {int state; gv_t globalVars;};")
                    println("vector<Token> tokens;")
                    println("  int numErrors;")
                    println("public:").nl()

                    println("${gtt.name.capitalize()}Monitor() { reset(); }")

                    cblock("void reset() override {", "}") {
                        print("""
                            this->state(MonitorState::FINE);
                            numErrors = 0;
                            tokens.clear();
                        """.trimIndent())
                        automaton.getStartStates().forEach {
                            val state = "${enumStates}::${it.name}".also {
                                createNewToken("tokens  ", it, "${structNameGv}_default")
                            }
                        }
                    }

                    cw.nl().cblock("void next(const io_t &input) override {", "}") {
                        print("""
                                vector<Token> newTokens;
                                for (auto &&tok : tokens) evaluate(newTokens, tok, input);
                            
                                tokens.clear();
                            
                                bool hitError = false, hitState = false;
                                for (auto &&i : newTokens) {
                                  switch (i.state) {
                                    case ERROR_STATE:
                                      hitError = true;
                                      break;
                                    case LIGHTNING_STATE:
                                      break;
                                    default: {
                                      hitState = true;
                                      tokens.push_back(i);
                                    }
                                  }
                                } 
                                this->state(hitError ? MonitorState::ERROR
                                               : hitState ? MonitorState::FINE : MonitorState::UNKNOWN);
                        """.trimIndent())
                    }

                    cw.nl().cblock("void evaluate (vector<Token> &newTokens, " +
                            "Token &token, const io_t &input) {",
                            "}") {
                        println("bool __inputcnstr = false, __outputcnstr = false;")
                        //println("bool newToken = false;")
                        cblock("switch(token.state) {", "}") {
                            automaton.rowStates.forEach { (tr, rs) ->
                                rs.forEach { println("case ${enumStates}::${it.name}:") }
                                increaseIndent()
                                nl().print("__inputcnstr = ${expr(tr.inputExpr)};")
                                nl().print("__outputcnstr  = ${expr(tr.outputExpr)};")

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

    private fun createNewToken(vec: String, state: String, globalvars: String) {
        cw.println("$vec.push_back((struct Token) " +
                "{ .state = $state, .globalVars = $globalvars });")
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
            createNewToken("newTokens", "$enumStates::$to", "token.globalVars")
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
        monitor.types += defineIOStruct("T_io_t", combinedVariables)
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
