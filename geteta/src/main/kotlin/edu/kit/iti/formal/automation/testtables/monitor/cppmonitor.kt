package edu.kit.iti.formal.automation.testtables.monitor


import edu.kit.iti.formal.automation.cpp.TranslateToCppFacade
import edu.kit.iti.formal.automation.cpp.TranslateToCppFacade.dataType
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.automation.testtables.model.automata.RowState
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.automation.testtables.model.automata.Transition
import edu.kit.iti.formal.automation.testtables.model.automata.TransitionType
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.ast.SBinaryExpression
import edu.kit.iti.formal.smv.ast.SBinaryOperator
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import edu.kit.iti.formal.smv.find
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.error
import edu.kit.iti.formal.util.joinInto
import edu.kit.iti.formal.util.warn
import java.util.*

val EMPTY_COLUMN = SVariable("ERROR", SMVTypes.BOOLEAN)

val CPP_HEADER by lazy { readResource("header.cpp").second }
val CPP_FOOTER by lazy { readResource("footer.cpp").second }
val CPP_RESOURCES by lazy { listOf(readResource("monitor.h")) }


/**
 * TODO double the state variable of the system (prev, next value).
 * @author Alexander Weigl
 * @version 1 (14.07.19)
 */
object CppMonitorGenerator : MonitorGeneration {
    override val key: String = "cpp"
    override fun generate(gtt: GeneralizedTestTable, automaton: TestTableAutomaton,
                          options: MonitorGenerationOptions): Monitor {
        val impl = CppMonitorGeneratorImpl(gtt, automaton)
        impl.includes = options.includes
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
    var includes = listOf<String>()
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
                    it.variableReplacement[ref.name] = "_h_${a.name.replace("code\$", "")}[$b]"
                }

                gtt.programVariables.forEach { pv ->
                    val name = pv.externalVariable(gtt.programRuns, gtt.name).name
                    it.variableReplacement[name] = "input.${pv.name}"
                }
                gtt.constraintVariables.forEach { cv ->
                    val name = cv.internalVariable(gtt.programRuns).name
                    it.variableReplacement[name] = "token.globalVars.${cv.name}"
                }
                println(it.variableReplacement)
                it.rewritingFunction = { it -> it.replace("code$", "input.") }
            }

    private val resetTrigger = gtt.options.monitor.resetTrigger?.let {
        val e = GetetaFacade.exprToSMV(it.trim('"'), EMPTY_COLUMN, 0, gtt.parseContext)
        e.accept(cppRewriter)
    }

    val dynamicTrigger = gtt.options.monitor.dynamicTrigger?.let {
        val e = GetetaFacade.exprToSMV(it, EMPTY_COLUMN, 0, gtt.parseContext)
        e.accept(cppRewriter)
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
                println("const struct $structNameGv ${structNameGv}_default = {};").nl().nl()
            }

    private fun defineStateEnum() = CodeWriter.with {
        cblock("enum class $enumStates {", "};") {
            val states = automaton.getRowStates() +
                    automaton.stateError + automaton.stateSentinel
            val rows = states.joinToString(", ") { it.name }
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
                    +("struct Token {int state; $structNameGv globalVars;};")
                    +("vector<Token> tokens;")
                    +("int numErrors;")
                    this.historyValuesDeclaration(gtt)
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
                        +"bool __assumption = false, __assertion = false;"
                        bindGlobalVariables()
                        switch("token.state") {
                            automaton.rowStates.forEach { (tr, rs) ->
                                rs.forEach { +"case ${enumStates}::${it.name}:" }
                                increaseIndent()
                                assertVariableBound(gtt, tr)
                                nl().print("__assumption = ${expr(tr.inputExpr)};")
                                nl().print("__assertion  = ${expr(tr.outputExpr)};")
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

        includes.forEach {
            monitor.preamble += "#include \"$it\"\n"
        }

        monitor.body = cw.stream.toString()
        return monitor
    }

    private fun CodeWriter.bindGlobalVariables() {
        for (gv in gtt.constraintVariables) {
            val gvsvar = gtt.parseContext.getSMVVariable(gv)
            ift("!token.globalVars.${gv.name}_bound") {
                switch("token.state") {
                    automaton.rowStates.forEach { (tr, rs) ->
                        (tr.inputExpr.values + tr.outputExpr.values).findAssignment(gvsvar)
                                ?.let { equality ->
                                    rs.forEach { +"case ${enumStates}::${it.name}:" }
                                    +"token.globalVars.${gv.name}_bound = true;"
                                    +"token.globalVars.${gv.name} = ${equality.accept(cppRewriter)};"
                                    +"break;"
                                }
                    }
                }
            }
        }
    }

    private fun resetCode(writer: CodeWriter) {
        resetTrigger?.let { cond ->
            writer.ift("$cond && state() == UNKNOWN") {
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
            TransitionType.ACCEPT -> "__assumption && __assertion"
            TransitionType.ACCEPT_PROGRESS ->
                "__assumption && __assertion"
            TransitionType.FAIL ->
                "__assumption && !__assertion"
            TransitionType.TRUE -> "true"
            TransitionType.MISS -> "! __assumption"
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

fun CodeWriter.assertVariableBound(gtt: GeneralizedTestTable, tableRow: TableRow) {
    val globalVars = tableRow.getUsedGlobalVariables(gtt)
    for (gv in globalVars) {
        +"assert(token.globalVars.${gv.name}_bound);"
    }
}


private fun Iterable<SVariable>.filterUsedVariables(seq: List<SMVExpr>): List<SVariable> =
        filter { gv -> seq.any { expr -> expr.find { it == gv } != null } }


/** Searches for equality of gv with other terms. TODO look only for top level formulas */
fun List<SMVExpr>.findAssignment(gv: SVariable): SMVExpr? {
    val getExpr: (SMVExpr) -> SMVExpr? = { eq: SMVExpr ->
        if (eq is SBinaryExpression) {
            if (eq.operator == SBinaryOperator.EQUAL) {
                when {
                    eq.left == gv -> eq.right
                    eq.right == gv -> eq.left
                    else -> null
                }
            } else {
                null
            }
        } else {
            null
        }
    }
    val pred = { eq: SMVExpr -> getExpr(eq) != null }
    val assignments = map { it.find(pred) }
            .filterNotNull().mapNotNull(getExpr)
            .toHashSet()

    if (assignments.size > 1) {
        warn("There are possible conflicting assignments for global variable $gv in one row. $assignments")
    }

    return assignments.firstOrNull()
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
        get() = subMonitors.asSequence().filter { !it.static }//.map { it.name }

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
                    subGenerators[index].dynamicTrigger?.let { ctrigger ->
                        val m = subMonitors[index]
                        ift(ctrigger) {
                            +("auto m = new ${m.name}();")
                            +("monitors.push_back(m);")
                        }
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
        get() = "_" + this.name.lowercase(Locale.getDefault())
}

private fun CodeWriter.historyValuesDeclaration(gtt: GeneralizedTestTable) {
    for ((a, b) in gtt.parseContext.refs) {
        if (b < 0) {
            val dt = TranslateToCppFacade.translate(a.dataType)
            +"sregister<$dt, ${-b}> _h_${a.name.replace("code\$", "")};"
        }
    }
}

private fun CodeWriter.historyValuesUpdate(gtt: GeneralizedTestTable) {
    for ((a, b) in gtt.parseContext.refs) {
        if (b > 0) {
            +"_h_${a.name}.push(input.${a.name.replace("code\$", "")});"
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
    cblock("case $cond:", "break", fn)
    return this
}


private fun readResource(name: String): Pair<String, String> {
    val content = CppMonitorGenerator.javaClass.getResourceAsStream("/monitor/$name")
            ?.use { it.bufferedReader().readText() }
    if (content == null) {
        error("Could not read resource: $name")
    }
    return name to (content ?: "")
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