package edu.kit.iti.formal.automation.testtables.monitor

import edu.kit.iti.formal.automation.cpp.TranslateToCppFacade
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.AnyInt
import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.st.ast.BooleanLit
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.apps.bindsConstraintVariable
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.Variable
import edu.kit.iti.formal.automation.testtables.model.automata.*
import edu.kit.iti.formal.smv.SMVAstDefaultVisitorNN
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.smv.conjunction
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.joinInto
import edu.kit.iti.formal.util.times
import java.io.StringWriter
import java.util.*
import java.util.concurrent.Callable

object CMonitorGenerator : MonitorGeneration {
    override val key = "c"

    override fun generate(gtt: GeneralizedTestTable, automaton: TestTableAutomaton): Monitor {
        val impl = CMonitorGeneratorImpl(gtt, automaton)
        return impl.call()
    }
}

private class CMonitorGeneratorImpl(val gtt: GeneralizedTestTable, val automaton: TestTableAutomaton,
                                    val compressState: Boolean = false,
                                    val useDefines: Boolean = false) : Callable<Monitor> {
    val monitor = Monitor()
    val stream = StringWriter()
    val writer = CodeWriter(stream)
    val state_t = "state_${gtt.name.toLowerCase()}_t"
    val inout_t = "inout_${gtt.name.toLowerCase()}_t"

    val userReset = "FORCE_RST"
    val error = "ERROR"
    val lostSync = "LOST_SYNC"
    val resets = "RESETS"

    val sUserReset = "io->FORCE_RST"
    val sError = "state->$error"
    val sLostSync = "state->$lostSync"
    val sResets = "state->RESETS"


    override fun call(): Monitor {
        header()
        declareStateType()
        declareInoutType()
        declareStateFunctions()
        declareInoutFunctions()
        declareFunUpdateMonitor()
        return monitor
    }


    fun header() {
        val asciiTable = GetetaFacade.print(gtt)
        stream.write("""
// Generated Monitor for table: ${gtt.name}.
// Generated at ${Date()}

/*
$asciiTable
*/

#include <stdint.h>

""".trimIndent())
    }

    val commentLine = "\n//" + (("-" * 78) as String) + "\n"

    fun declareStateType() {
        writer.nl().write(commentLine)
                .write("// Structure for internal state of the monitor.")
                .nl()

        writer.cblock("struct $state_t {", "}") {
            writer.print("//global variables").nl()
            gtt.constraintVariables
                    .joinInto(this, "\n") {
                        "${it.ctype} ${it.name};\n"
                    }

            gtt.constraintVariables
                    .joinInto(this, "\n") {
                        "    int8_t ${it.name}_bound" + (if (compressState) " : 1 " else "") + ";"
                    }

            automaton.rowStates.values.flatMap { it }.joinInto(writer) {
                "    int8_t ${it.name} " + (if (compressState) " : 1 " else "") + ";"


            }
        }
    }

    fun declareInoutType(): Unit {
        writer.nl().write(commentLine)
                .write("// Structure for the input and output of the monitor.")
                .nl()

        writer.cblock("struct $inout_t {", "}") {
            gtt.programVariables.joinInto(writer, "\n") {
                "${it.ctype} ${it.name};"
            }
        }
    }

    /*gtt.programVariables.joinInto(writer, "\n"){
                    "io->${it.name} = ${it.cInitValue};"
                }*/
    fun declareInoutFunctions() {
        writer.write("""


            /*
             *  ...
             */
            void init_$inout_t($inout_t* io) {
                memset(io, 0, sizeof($inout_t));
            }


            /*
             *  ...
             */
            $inout_t* new_$inout_t() {
                        $inout_t* io = ($inout_t*) malloc(sizeof($inout_t));
                        init_$inout_t(io)
                        return io
            }


            /*
             *  Frees the memory.
             */
            void free_$inout_t($inout_t* io) {
                free(io);
            }

        """.trimIndent())
    }

    fun declareStateFunctions() {


        writer.write("""

            /*
                Function initialize the given $state_t structure with default values.
            */

        """.trimIndent())

        writer.cblock("void init_$state_t($state_t* state) {", "}") {
            gtt.constraintVariables.joinInto(this, "") {
                nl()
                write("state->${it.name} = ${it.cInitValue};")
            }

            gtt.constraintVariables.joinInto(this, "") {
                nl()
                write("state->${it.name} = 0;")
            }

            automaton.rowStates.values.flatMap { it }.joinInto(writer, "") {
                val initValue = if (it in automaton.initialStates) "1" else "0"
                nl().write("state->${it.name} = $initValue;")
            }
        }


        writer.write("""


            /*
             *  Creates a new state for monitor of ${gtt.name}.
             */

        """.trimIndent())


        stream.write("""
            $state_t* new_$state_t() {
                $state_t* state = ($state_t*) malloc(sizeof($state_t));
                init_$state_t(state)
                return state
            }
        """.trimIndent())


        writer.write("""


            /*
             *  Frees the memory.
             */

        """.trimIndent())


        stream.write("""
            void free_$state_t($state_t* state) {
                free(state);
            }
        """.trimIndent())

    }

    fun declareFunUpdateMonitor() {
        declareAuxVariables(false)
        writer.nl().nl()

        writer.write("""


            /*
             *  Update the internal state of the memory.
             */

        """.trimIndent())

        writer.cblock("void update_monitor($state_t* state, $inout_t* io) {", "}") {
            bindFreeVariables()
            writer.write(commentLine)
            declareAuxVariables(true)
            writer.write(commentLine)
            updateStateVariables()
            writer.write(commentLine)
            resets()
            writer.write(commentLine)
            updateOutput()
        }
    }

    private fun bindFreeVariables() {
        gtt.constraintVariables.forEach { fvar ->
            val boundFlag = "state->${fvar.name}_bound"
            automaton.rowStates.forEach { row, states ->
                val oneOfRowStates = states.map { "state->${it.name}" }
                row.rawFields.forEach { pvar, ctx ->
                    val bind = bindsConstraintVariable(ctx, fvar)
                    if (bind) {
                        writer.nl()
                        writer.cblock("if(!$boundFlag && $oneOfRowStates) {", "}") {
                            writer.write("${fvar.name} = ${pvar.name};")
                                    .nl().write("$boundFlag = 1;")

                        }
                    }
                }
            }
        }
    }

    private fun updateOutput() {
        val noStateOccupied = automaton.rowStates.values.flatMap { it }
                .map { it.name }
                .reduce { a: String, b: String -> "$a || $b" }

        writer.write("$sLostSync = !($noStateOccupied);")
                .nl()
                .write("$sError = ($sLostSync && state->${automaton.stateError.name});")
    }

    private fun resets() {
        val inputs = automaton.initialStates
                .map { (it as RowState).row.defInput.name }
                .reduce { a: String, b: String -> "$a || $b" }
        writer.cblock("if(${sLostSync} && $inputs) ||| $sUserReset) {", "}") {
            write("init_$state_t(state);")
            nl().write("${sResets} += 1;")

        }
    }

    private fun updateStateVariables() {
        val transitions = automaton.transitions.groupBy { it.to }
        automaton.rowStates.values.flatMap { it }.forEach { createNext(transitions, it) }
        createNext(transitions, automaton.stateError)
        createNext(transitions, automaton.stateSentinel)
    }

    private fun createNext(transitions: Map<AutomatonState, List<Transition>>, it: AutomatonState) {
        val to = it.name
        val expr = transitions[it]?.map { t ->
            val from = t.from as? RowState
            val fromName = t.from.name
            when (t.type) {
                TransitionType.ACCEPT ->
                    from!!.row.defInput.name + " && " + fromName
                TransitionType.ACCEPT_PROGRESS ->
                    from!!.row.defProgress.name + " && " + fromName
                TransitionType.FAIL ->
                    from!!.row.defFailed.name + " && " + fromName
                TransitionType.TRUE ->
                    fromName
            }
        }?.reduce { a, b -> "$a || $b" }
                ?: BooleanLit.LFALSE
        writer.nl().write("$to = $expr;")
    }

    private fun declareAuxVariables(localVars: Boolean) {
        if (localVars && !useDefines) {
            automaton.rowStates.forEach { tr, rs ->
                val defInput = (tr.defInput.name)
                val defOutput = (tr.defOutput.name)
                val defFailed = (tr.defFailed.name)
                val defForward = (tr.defForward.name)
                val defProgress = (tr.defProgress.name)

                val progress = tr.outgoing.map { it.defInput.name }
                        .reduce { acc: String, v: String -> "$acc || $v" }

                writer.write("int8_t $defInput  = ${tr.inputExpr.values.conjunction().toCExpression()};")
                        .nl()
                        .write("int8_t $defOutput  = ${tr.outputExpr.values.conjunction().toCExpression()};")
                        .nl()
                        .write("int8_t $defFailed = ($defInput && !$defOutput);")
                        .nl()
                        .write("int8_t $defForward = ($defInput && $defOutput);")
                        .nl()
                        .write("int8_t $defProgress = (($defInput && $defOutput) && !$progress);")
            }
        }

        if (!localVars && useDefines) {
            automaton.rowStates.forEach { tr, rs ->
                val defInput = (tr.defInput.name)
                val defOutput = (tr.defOutput.name)
                val defFailed = (tr.defFailed.name)
                val defForward = (tr.defForward.name)
                val defProgress = (tr.defProgress.name)

                val progress = tr.outgoing.map { it.defInput.name }
                        .reduce { acc: String, v: String -> "$acc || $v" }

                writer.write("#define   $defInput  = (${tr.inputExpr.values.conjunction().toCExpression()});")
                        .nl()
                        .write("#define $defOutput  = (${tr.outputExpr.values.conjunction().toCExpression()});")
                        .nl()
                        .write("#define $defFailed = ($defInput && !$defOutput);")
                        .nl()
                        .write("#define $defForward = ($defInput && $defOutput);")
                        .nl()
                        .write("#define $defProgress = (($defInput && $defOutput) && !$progress);")
            }
        }
    }
}

private fun SMVAst.toCExpression(): String = accept(SmvToCTranslator())

private val Variable.cInitValue: String
    get() {
        val dt = dataType
        return when (dt) {
            is AnyBit.BOOL -> "0"
            is AnyInt -> "0"
            is EnumerateType -> "0"
            else -> "$dt is unknown"
        }
    }

private val Variable.ctype: String
    get() = TranslateToCppFacade.dataType(dataType)
/*return when (dt) {
    is AnyBit.BOOL -> "int8_t";
    is AnyInt ->
        if (dt.isSigned)
            "int${dt.bitLength}_t";
        else
            "uint${dt.bitLength}_t";
    is EnumerateType ->
        "uint8_t";
    else -> "$dt is unknown"
}*/


class SmvToCTranslator : SMVAstDefaultVisitorNN<String>() {
    override fun defaultVisit(top: SMVAst): String = "/*$top not supported*/"
    val variableReplacement = HashMap<String, String>()
    val rewritingFunction = { n: String -> n }
    override fun visit(v: SVariable): String {
        val n = variableReplacement[v.name] ?: v.name
        return rewritingFunction(n)
    }

    override fun visit(ue: SUnaryExpression) =
            "(${opToC(ue.operator)} ${ue.expr.accept(this)})"

    override fun visit(be: SBinaryExpression) =
            "(${be.left.accept(this)} ${opToC(be.operator)} ${be.right.accept(this)})"

    private fun opToC(operator: SBinaryOperator) = when (operator) {
        SBinaryOperator.PLUS -> "+"
        SBinaryOperator.MINUS -> "-"
        SBinaryOperator.DIV -> "/"
        SBinaryOperator.MUL -> "*"
        SBinaryOperator.AND -> " && "
        SBinaryOperator.OR -> " || "
        SBinaryOperator.LESS_THAN -> " < "
        SBinaryOperator.LESS_EQUAL -> " <= "
        SBinaryOperator.GREATER_THAN -> " > "
        SBinaryOperator.GREATER_EQUAL -> " >="
        SBinaryOperator.XOR -> " ^ "
        SBinaryOperator.XNOR -> TODO()
        SBinaryOperator.EQUAL -> " == "
        SBinaryOperator.IMPL -> TODO()
        SBinaryOperator.EQUIV -> " == "
        SBinaryOperator.NOT_EQUAL -> " != "
        SBinaryOperator.MOD -> " % "
        SBinaryOperator.SHL -> " << "
        SBinaryOperator.SHR -> " >> "
        SBinaryOperator.WORD_CONCAT -> TODO()
    }

    private fun opToC(operator: SUnaryOperator): String {
        return when (operator) {
            SUnaryOperator.MINUS -> "-"
            SUnaryOperator.NEGATE -> "!"
            else -> "<unknown unary operator>"
        }
    }

    override fun visit(l: SLiteral) = l.value.toString()

    override fun visit(ce: SCaseExpression): String {
        val sb = StringBuilder()
        ce.cases.forEach {
            sb.append("${it.condition.accept(this)} ? (${it.then.accept(this)}) : ");
        }
        sb.append("assert(false)")
        return sb.toString()
    }

    override fun visit(func: SFunction) = "${func.name}(${func.arguments.joinToString(", ") { it.accept(this) }})"
}