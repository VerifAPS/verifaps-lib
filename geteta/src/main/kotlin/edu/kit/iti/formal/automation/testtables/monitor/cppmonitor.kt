package edu.kit.iti.formal.automation.testtables.monitor

import edu.kit.iti.formal.automation.Console
import edu.kit.iti.formal.automation.cpp.TranslateToCppFacade
import edu.kit.iti.formal.automation.cpp.TranslateToCppFacade.dataType
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.model.ColumnVariable
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

val EMPTY_COLUMN = SVariable("ERROR", SMVTypes.BOOLEAN)

val CPP_HEADER by lazy { readResource("header.cpp").second }
val CPP_FOOTER by lazy { readResource("footer.cpp").second }
val CPP_RESOURCES by lazy { listOf(readResource("monitor.hpp")) }


/**
 * TODO double the state variable of the system (prev, next value).
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

object CppCombinedMonitorGeneration : CombinedMonitorGeneration {
    override fun generate(name: String, input: List<Pair<GeneralizedTestTable, TestTableAutomaton>>): Monitor {
        return CppCombinedMonitorGenerationImpl(name, input).call()
    }

    override val key = "cpp"
}


class CppMonitorGeneratorImpl(val gtt: GeneralizedTestTable, val automaton: TestTableAutomaton) {
    val monitor = Monitor(gtt.name, "", "")
    val cw = CodeWriter()

    val structNameIo = "${gtt.name}_io_t"
    val structNameGv = "${gtt.name}_gv_t"
    val enumStates = "${gtt.name.capitalize()}States"
    val cppRewriter =
            SmvToCTranslator().also {
                //val re = "(.+)\\.\\_\\$(\\d+)".toRegex()
                for ((a, b) in gtt.parseContext.refs) {
                    val ref = gtt.parseContext.getReference(a, b)
                    it.variableReplacement[ref.name] = "_h_${a.name}[b]"
                }

                gtt.programVariables.forEach { pv ->
                    val name = pv.externalVariable(gtt.programRuns, gtt.name).name
                    it.variableReplacement[name] = "input.${pv.name}"
                }
                gtt.constraintVariables.forEach { cv ->
                    val name = cv.externalVariable(gtt.programRuns, gtt.name).name
                    it.variableReplacement[name] = "token.globalVars.${cv.name}"
                }

                it.rewritingFunction = { it -> it.replace("code$", "input.") }
            }

    private fun defineGlobalVarStruct() =
            CodeWriter.with {
                cblock("struct $structNameGv {", "};") {
                    gtt.constraintVariables.forEach { pv ->
                        println("${dataType(pv.dataType)}  ${pv.name};")
                    }
                    gtt.constraintVariables.forEach { pv ->
                        println("bool is_bound_${pv.name};")
                    }
                }.nl()
                println("const struct $structNameGv ${structNameGv}_default;").nl().nl()
            }

    private fun defineStateEnum() = CodeWriter.with {
        cblock("enum $enumStates {", "};") {
            val states = automaton.getRowStates() +
                    automaton.stateError + automaton.stateSentinel
            val rows = states.joinToString(",") { it.name }
            append(rows)
        }
        nl().nl()
    }

    fun call(): Monitor {
        monitor.types += defineIOStruct(structNameIo, gtt.programVariables)
        monitor.types += defineGlobalVarStruct()
        monitor.types += defineStateEnum()

        cw.println("template <typename io_t>")
                .cblock("class ${gtt.name.capitalize()}Monitor " +
                        ": public IMonitor<io_t> {", "};") {
                    +("struct Token {int state; gv_t globalVars;};")
                    +("vector<Token> tokens;")
                    +("int numErrors;")
                    historyValuesDeclaration(gtt)
                    +"public:"

                    constructor("${gtt.name.capitalize()}Monitor") { +"reset();" }

                    method("void", "reset", "override") {
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

                    nl().method("void", "next", "const io_t &input", "override") {
                        resetCode(this)
                        +"""
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
                        """.trimIndent()
                        historyValuesUpdate(gtt)
                    }

                    nl().method("void", "evaluate",
                            "vector<Token> &newTokens", "Token &token", "const io_t &input") {
                        +"bool __inputcnstr = false, __outputcnstr = false;"
                        switch("token.state") {
                            automaton.rowStates.forEach { (tr, rs) ->
                                rs.forEach { +"case ${enumStates}::${it.name}:" }
                                increaseIndent()
                                nl().print("__inputcnstr = ${expr(tr.inputExpr)};")
                                nl().print("__outputcnstr  = ${expr(tr.outputExpr)};")
                                nl().switch("token.state") {
                                    rs.forEach { generateCase(it) }
                                }
                                +"break;"
                                decreaseIndent()
                            }
                        }
                    }
                }

        monitor.postamble = CPP_FOOTER
        monitor.preamble = CPP_HEADER
        monitor.body = cw.stream.toString()
        return monitor
    }

    private fun resetCode(writer: CodeWriter) {
        gtt.options.monitor.resetTrigger?.let { cond ->
            val sexpr = GetetaFacade.exprToSMV(cond, EMPTY_COLUMN, 0, gtt.parseContext)
            val expr = sexpr.accept(cppRewriter)
            writer.cblock("if($expr && state() == UNKNOWN) {", "}") {
                +"reset()"
            }
        }
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

class CppCombinedMonitorGenerationImpl(
        val name: String,
        val input: List<Pair<GeneralizedTestTable, TestTableAutomaton>>,
        val aggregation: String = "CombinedAndMonitor") {

    private val containsDynamic =
            input.any { (a, b) -> !a.options.monitor.dynamicTrigger.isNullOrBlank() }

    private val subGenerators = input.map { (a, b) -> CppMonitorGeneratorImpl(a, b) }
    private val subMonitors = subGenerators.map { g -> g.call() }

    private val staticMonitors
        get() = subMonitors.asSequence().filter { it.static }//.map { it.name }

    private val dynamicMonitors
        get() = subMonitors.asSequence().filter { it.static }//.map { it.name }

    private val monitor = Monitor()

    fun call(): Monitor {
        generate()
        return monitor
    }

    private fun generate() {
        inputStruct()
        val ownBody = getOwnBody()
        monitor.body = subMonitors.joinToString("\n\n") { it.body } + ownBody
        monitor.preamble = CPP_HEADER
        monitor.postamble = CPP_FOOTER
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
        monitor.types += subMonitors.joinToString("\n") { it.types }
        monitor.types += defineIOStruct("${name}_io_t", combinedVariables)
    }

    private fun getOwnBody(): String =
            CodeWriter.with {
                cblock("class $name : public $aggregation<io_t> {", "};") {
                    if (containsDynamic)
                        +"vector<IMonitor<io_t> *> monitors;"

                    staticMonitors.forEach { +"${it.name} ${it.instanceName};" }

                    +"public:"
                    genConsructor()
                    genReset()
                    genEval()
                    genBefore()
                    genAfter()
                }
            }

    private fun CodeWriter.genAfter() {
        method("void", "cleanup", "override") {
            +"""            
            auto pred = [](IMonitor<io_t> *m) {
                return /*m->is(DYNAMIC) &&*/ m->state() == UNKNOWN;
            };
            vector<IMonitor<io_t> *> forDeletion(monitors.size());
            copy_if(monitors.begin(), monitors.end(), forDeletion.begin(), pred);
            for (auto m : forDeletion) { delete m; }
            remove_if(monitors.begin(), monitors.end(), pred);
            """.trimIndent()
        }
    }

    private fun CodeWriter.genBefore() {
        method("void", "before", "const io_t &input", "override") {
            input.forEachIndexed { index, (a, b) ->
                a.options.monitor.dynamicTrigger?.let { trigger ->
                    val m = subMonitors[index]
                    val e = GetetaFacade.exprToSMV(trigger, EMPTY_COLUMN, 0, a.parseContext)
                    val ctrigger = e.accept(subGenerators[index].cppRewriter)
                    ift(ctrigger) {
                        println("auto m = new ${m.name}();")
                        println("monitors.push_back(m);")
                    }
                }
            }
        }
    }

    private fun CodeWriter.genEval() {
        method("void", "eval", "const io_t &input", "override") {
            staticMonitors.forEach {
                val n = it.instanceName
                +"$n.next(input); combine(${n}.state());"
            }
            if (containsDynamic)
                println("for(auto& m: monitors) {m->next(input); combine(m->state());}")
        }
    }

    private fun CodeWriter.genConsructor() {
        val init = staticMonitors.toList().map { "${it.instanceName}()" }
        constructor(name, init) { +"reset();" }
        method("", "~$name") { +"for (auto m : forDeletion) { delete m; }" }
    }

    private fun CodeWriter.genReset() {
        method("virtual void", "reset", "override") {
            if (containsDynamic)
                +"for (auto m : monitors) m->reset();"
            subMonitors.forEach {
                +"${it.instanceName}.reset();"
            }
        }
    }

    private val Monitor.instanceName: String
        get() = "_" + this.name.toLowerCase()
}

private fun CodeWriter.historyValuesDeclaration(gtt: GeneralizedTestTable) {
    for ((a, b) in gtt.parseContext.refs) {
        if (b > 0) {
            val dt = TranslateToCppFacade.translate(a.dataType)
            +"sregister<$dt, $b> ${a.name};"
        }
    }
}

private fun CodeWriter.historyValuesUpdate(gtt: GeneralizedTestTable) {
    for ((a, b) in gtt.parseContext.refs) {
        if (b > 0) {
            +"_h_${a.name}.push(input.${a.name});"
        }
    }
}


private fun CodeWriter.constructor(name: String, inits: Iterable<String> = listOf(), fn: CodeWriter.() -> Unit): CodeWriter {
    val a = inits.joinToString(", ")
    val b = if (a.isBlank()) "" else ": $a"
    cblock("$name() $b {", "}", fn)
    return this
}

private fun CodeWriter.method(ret: String = "", name: String,
                              args: Iterable<String>, fn: CodeWriter.() -> Unit) {
    val params = args.filter { ' ' in it }.joinToString(", ")
    val mods = args.filter { ' ' !in it }.joinToString(" ")
    cblock("$ret $name($params) $mods {", "}", fn)
}

private fun CodeWriter.method(ret: String = "", name: String,
                              vararg args: String, fn: CodeWriter.() -> Unit) = method(ret, name, args.toList(), fn)

private fun CodeWriter.ift(cond: String = "", fn: CodeWriter.() -> Unit): CodeWriter {
    cblock("if($cond) {", "}", fn)
    return this
}

private fun CodeWriter.e(cond: String = "", fn: CodeWriter.() -> Unit) {
    cblock("else {", "}", fn)
}

private fun CodeWriter.switch(cond: String, fn: CodeWriter.() -> Unit): CodeWriter {
    cblock("switch($cond) {", "}", fn)
    return this
}

private fun CodeWriter.case(cond: String, fn: CodeWriter.() -> Unit): CodeWriter {
    cblock("case $cond:", "", fn)
    return this
}


private fun readResource(name: String): Pair<String, String> {
    val content = CppMonitorGenerator.javaClass.getResourceAsStream("/monitor/$name")
            ?.use { it.bufferedReader().readText() }
    if(content == null)
    {
        Console.error("Could not read resource: $name")
    }
    return name to (content?:"")
}

private fun defineIOStruct(typeName: String, variables: MutableList<ColumnVariable>): String =
        CodeWriter.with {
            cblock("struct $typeName {", "};") {
                variables.filterIsInstance<ProgramVariable>()
                        .forEach { pv ->
                            print("${dataType(pv.dataType)}  ${pv.name};")
                                    .println("// ${pv.category}")
                        }
            }
            nl().nl()
        }