package edu.kit.iti.formal.automation.testtables.model

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.st.ArrayLookupList
import edu.kit.iti.formal.automation.st.Identifiable
import edu.kit.iti.formal.automation.st.LookupList
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.apps.Geteta
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.options.TableOptions
import edu.kit.iti.formal.automation.testtables.rtt.VARIABLE_PAUSE
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.VariableReplacer
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*
import kotlin.collections.ArrayList
import kotlin.collections.HashMap


enum class ColumnCategory { ASSUME, ASSERT }

sealed class Variable : Identifiable {
    abstract override var name: String
    abstract var dataType: AnyDt
    abstract var logicType: SMVType

    open fun externalVariable(programRunNames: List<String>, tableName: String) = internalVariable(programRunNames).inModule(tableName)

    open fun internalVariable(programRunNames: List<String>) = SVariable(name, logicType)
}

abstract class ColumnVariable(open var category: ColumnCategory = ColumnCategory.ASSUME) : Variable() {
    val isAssumption
        get() = category == ColumnCategory.ASSUME

    val isAssertion
        get() = !isAssumption

    abstract fun respondTo(name : String, run : Int?) : Boolean
}

data class ProgramVariable(
        override var name: String,
        override var dataType: AnyDt,
        override var logicType: SMVType,
        override var category: ColumnCategory = ColumnCategory.ASSUME,
        var isState: Boolean = false,
        var isNext: Boolean = false,
        var programRun: Int = 0) : ColumnVariable(category) {

    override fun respondTo(name: String, run: Int?)
            = name == this.name && (run==null || programRun == run)

    var realName: String = name
    /**
     *
     */
    override fun externalVariable(programRunNames: List<String>, tableName: String) =
            SVariable("${programRunNames[programRun]}.$realName", logicType)

    /**
     *
     */
    override fun internalVariable(programRunNames: List<String>): SVariable = SVariable("${programRunNames[programRun]}$realName", logicType)
}

data class ConstraintVariable(
        override var name: String,
        override var dataType: AnyDt,
        override var logicType: SMVType,
        var constraint: TestTableLanguageParser.CellContext? = null)
    : Variable()

data class ProjectionVariable(
        override var name: String,
        override var dataType: AnyDt,
        override var logicType: SMVType,
        override var category: ColumnCategory = ColumnCategory.ASSUME,
        var constraint: MutableList<TestTableLanguageParser.ExprContext> = arrayListOf())
    : ColumnVariable(category) {

    val arity : Int
        get() = constraint.size

    val argumentDefinitions : List<SVariable>
        get()  = (0 until arity).map { SVariable("${name}_$it") }


    override fun respondTo(name: String, run: Int?)
            = name == this.name

    /**
     *
     */
    override fun externalVariable(programRunNames: List<String>, tableName: String) =
            SVariable("$tableName.$name", logicType)

    /**
     *
     */
    override fun internalVariable(programRunNames: List<String>): SVariable = SVariable("$name", logicType)
}

data class SmvFunctionDefinition(val body : SMVExpr, val parameter : List<SVariable>) {
    val arity = parameter.size
    fun call(args : List<SMVExpr>): SMVExpr {
        val replacement = parameter.zip(args).toMap()
        val replacer = VariableReplacer(replacement)
        return body.clone().accept(replacer) as SMVExpr
    }
}

class ParseContext(
        val relational: Boolean = false,
        val programRuns: List<String> = listOf(),
        val vars: MutableMap<Variable, SVariable> = hashMapOf(),
        val refs: MutableMap<SVariable, Int> = hashMapOf(),
        val functions : MutableMap<String, SmvFunctionDefinition> = hashMapOf(),
        val fillers: MutableMap<ColumnVariable, TestTableLanguageParser.CellContext> = hashMapOf()) {

    public fun isVariable(v: String) = v in this
    public fun getSMVVariable(v: Variable) =
            vars.computeIfAbsent(v) { v.internalVariable(programRuns) }

    fun getReference(columnVariable: SVariable, i: Int): SMVExpr {
        if (i == 0) {
            return columnVariable
        } else {
            val ref = SReference(i, columnVariable)
            val max = Math.max(refs.getOrDefault(columnVariable, i), i)
            refs[columnVariable] = max
            return ref.asVariable()
        }
    }

    operator fun contains(varText: String) = vars.keys.any { it.name == varText }

    fun getSMVVariable(programRun: Int?, v: String): SVariable {
        val globalVar = vars.keys.find { it.name == v }
        if (globalVar != null && globalVar is ConstraintVariable) {
            return getSMVVariable(globalVar)
        }

        val va = if (programRun != null)
            vars.keys.find { it.name == v && (it as? ProgramVariable)?.programRun == programRun }
                    ?: throw IllegalArgumentException("Could not find a variable for $programRun|>$v in signature.")
        else
            vars.keys.find { it.name == v }
                    ?: throw IllegalArgumentException("Could not find a variable for $v in signature.")

        return getSMVVariable(va)
    }

    fun getFunction(varName: String?): SmvFunctionDefinition? {
        return functions[varName] ?: findDefaultFunction(varName)
    }

    private fun findDefaultFunction(varName: String?): SmvFunctionDefinition? {
        if(varName==null) return null
        if(isVariable(varName)) return null

        return GetetaFacade.DEFAULT_COMPARISON_FUNCTIONS[varName]
    }
}

class GeneralizedTestTable(
        var name: String = "anonym",
        val programVariables: MutableList<ColumnVariable> = ArrayList(),
        val constraintVariables: MutableList<ConstraintVariable> = ArrayList(),
        var properties: MutableMap<String, String> = HashMap(),
        var region: Region = Region(0),
        val functions: LookupList<FunctionDeclaration> = ArrayLookupList(),
        var programRuns: List<String> = arrayListOf()
) {
    val options: TableOptions by lazy {
        TableOptions(properties)
    }

    fun clearReachability() {
        for (s in this.region.flat()) {
            s.outgoing.clear()
            s.incoming.clear()
            /*s.automataStates.clear()

            for (a in s.automataStates) {
                a.outgoing.clear()
                a.incoming.clear()
            }*/
        }
    }

    /*fun getSMVVariable(text: ProgramVariable): SVariable = getSMVVariable(text.name)
    override fun getSMVVariable(text: String): SVariable {
        return variableMap.computeIfAbsent(text) { k ->
            IOFacade.asSMVVariable(getVariable(k))
        }
    }*/

    /*fun isVariable(text: String) = text in programVariables || text in constraintVariables
    private fun getVariable(text: String): Variable {
        val a = programVariables[text]
        val b = constraintVariables[text]

        if (a != null && b != null)
            throw IllegalStateException(
                    "constraint and io variable have the same name.")

        return a ?: b ?: error("Could not found a variable with $text in signature.")
    }*/

    fun add(v: ColumnVariable) {
        programVariables += v
    }

    fun add(v: ConstraintVariable) {
        constraintVariables += v
    }

    fun addOption(key: String, value: String) {
        properties[key] = value
    }

    val DEFAULT_CELL_CONTENT = "-"

    fun generateSmvExpression(): ParseContext {
        region.flat().forEach {
            it.generateSmvExpression(parseContext)
        }
        return parseContext
    }

    val parseContext: ParseContext by lazy {
        val vc = ParseContext(options.relational, programRuns)
        constraintVariables.forEach {
            vc.getSMVVariable(it)
        }
        programVariables.forEach {
            vc.getSMVVariable(it)
            vc.fillers[it] = GetetaFacade.parseCell(DEFAULT_CELL_CONTENT).cell()
        }

        functions.forEach { fd ->
            vc.functions[fd.name] = GetetaFacade.functionToSmv(fd)
        }

        vc
    }
    val maxProgramRun: Int
        get() = programVariables
                .filterIsInstance(ProgramVariable::class.java)
                .map { it.programRun }.maxBy { it } ?: 0

    fun getProgramVariables(name: String, run: Int?): ColumnVariable {
        val pv = programVariables.find { it.respondTo(name, run) }
        return pv ?: throw IllegalStateException("Could not find variable: $run|>$name.")
    }

    fun ensureProgramRuns() {
        val max = 1 + maxProgramRun
        if (max == 1 && programRuns.isEmpty()) {
            programRuns += "code\$"
        } else {
            while (programRuns.size < max) {
                programRuns += "_${programRuns.size}\$"
            }
        }
    }

    fun getTableRow(rowId: String) = region.flat().find { it.id == rowId }
    fun isProgramVariable(variable: String): Boolean = programVariables.any { it.name == variable }
    fun isConstraintVariable(variable: String): Boolean = constraintVariables.any { it.name == variable }
}

operator fun <T : Identifiable> Iterable<T>.get(text: String) = find { it.name == text }
operator fun <T : Identifiable> Iterable<T>.contains(text: String) = this[text] != null


sealed class Duration {
    object Omega : Duration() {
        override fun contains(cycles: Int): Boolean = true

        override val isUnbounded: Boolean
            get() = true
        override val isOneStep: Boolean
            get() = false
        override val isSkippable: Boolean
            get() = false
        override val isRepeatable: Boolean
            get() = true
    }

    data class OpenInterval(val lower: Int, var pflag: Boolean = false) : Duration() {
        override fun contains(cycles: Int): Boolean = lower <= cycles

        override val isUnbounded: Boolean
            get() = true
        override val isOneStep: Boolean
            get() = false
        override val isSkippable: Boolean
            get() = lower == 0
        override val isRepeatable: Boolean
            get() = true
    }

    data class ClosedInterval(val lower: Int, val upper: Int, val pflag: Boolean = false) : Duration() {
        override fun contains(cycles: Int): Boolean = cycles in lower..upper

        override val isUnbounded: Boolean
            get() = false
        override val isOneStep: Boolean
            get() = lower == 1 && upper == 1
        override val isSkippable: Boolean
            get() = lower == 0
        override val isRepeatable: Boolean
            get() = !isOneStep
    }

    /**
     * returns true, iff the step can be applied arbitrary often (no upper bound)
     * @return
     */
    abstract val isUnbounded: Boolean

    /**
     * returns true, iff the step is applied only once
     * @return
     */
    abstract val isOneStep: Boolean

    /**
     * returns true, if the step can be overjumped directly
     *
     * @return
     */
    abstract val isSkippable: Boolean

    /**
     *
     * @return true iff this row can be applied more than once.
     */
    abstract val isRepeatable: Boolean

    /**
     * checks if the given integer lies within the duration
     *
     * @param cycles
     * @return
     */
    abstract operator fun contains(cycles: Int): Boolean
}


fun Duration.repr(): String =
        when (this) {
            is Duration.ClosedInterval -> "[$lower, $upper]"
            Duration.Omega -> "omega"
            is Duration.OpenInterval -> ">=$lower"
        }

fun Duration.isOptional(time: Int): Boolean =
        when (this) {
            is Duration.ClosedInterval -> lower <= time
            Duration.Omega -> false
            is Duration.OpenInterval -> lower <= time
        }


sealed class TableNode(open var id: String, var duration: Duration = Duration.ClosedInterval(1, 1, false)) {
    abstract fun count(): Int
    abstract fun flat(): List<TableRow>
    abstract fun depth(): Int
    abstract fun clone(): TableNode
}

data class Region(override var id: String,
                  var children: MutableList<TableNode> = arrayListOf()) : TableNode(id) {
    constructor(id: Int) : this("$id")

    override fun count(): Int = this.children.sumBy { it.count() }
    override fun flat(): List<TableRow> = this.children.flatMap { a -> a.flat() }
    override fun depth() = 1 + (this.children.maxBy { it.depth() }?.depth() ?: 0)
    override fun clone(): TableNode = copy().also { it.id = id; it.duration = duration }
}

data class TableRow(override var id: String) : TableNode(id) {
    val rawFields: MutableMap<ColumnVariable, TestTableLanguageParser.CellContext?> = linkedMapOf()

    /** Input constraints as list. */
    val inputExpr: MutableMap<String, SMVExpr> = hashMapOf()

    /** Output constraints as list. */
    val outputExpr: MutableMap<String, SMVExpr> = hashMapOf()

    /** incoming rowStates */
    val incoming: MutableSet<TableRow> = HashSet()

    /** outgoing rowStates */
    val outgoing: MutableSet<TableRow> = HashSet()

    val defOutput = SVariable("${id}_out", SMVTypes.BOOLEAN)
    val defForward = SVariable("${id}_fwd", SMVTypes.BOOLEAN)
    val defFailed = SVariable("${id}_fail", SMVTypes.BOOLEAN)
    val defInput = SVariable("${id}_in", SMVTypes.BOOLEAN)

    /**
     * The predicate that allows keeping in this state.
     * Only necessary iff duration has progress flag.
     */
    val defProgress = SVariable("${id}_progress", SMVTypes.BOOLEAN)

    /**
     * name of runs to pause in that specific state.
     */
    var pauseProgramRuns: MutableList<Int> = arrayListOf()

    /*override val automataStates: MutableList<AutomatonState> = ArrayList()
        get() {
            if (field.isEmpty()) {
                val duration = duration
                when (duration) {
                    is Duration.Omega ->
                        field.add(AutomatonState(1))
                    is Duration.OpenInterval ->
                        for (i in 1..duration.lower)
                            field.add(AutomatonState(i))
                    is Duration.ClosedInterval ->
                        for (i in 1..duration.upper) {
                            field.add(AutomatonState(i))
                        }
                }
            }
            assert(field.size != 0)
            return field
        }
    */

    var isInitialReachable: Boolean = false
    var isEndState: Boolean = false

    constructor(id: Int) : this(id.toString())

    override fun count(): Int = 1
    override fun flat(): List<TableRow> = listOf(this)
    override fun depth(): Int = 0

    fun generateSmvExpression(vc: ParseContext) {
        inputExpr.clear()
        outputExpr.clear()

        val new = HashMap<ColumnVariable, TestTableLanguageParser.CellContext>()
        for (k in vc.fillers.keys.toHashSet()) {
            val v = rawFields[k]
            if (v != null) {
                vc.fillers[k] = v
                new[k] = v
            } else {
                val w = vc.fillers[k]
                if (w != null) new[k] = w
            }
        }
        rawFields.putAll(new)

        inputExpr.putAll(GetetaFacade.exprsToSMV(vc, new.filter { it.key.isAssumption }))
        outputExpr.putAll(GetetaFacade.exprsToSMV(vc, new.filter { it.key.isAssertion }))

        if (vc.relational)
            vc.programRuns.mapIndexed { i, s ->
                val pexpr = if (i in pauseProgramRuns)
                    vc.getSMVVariable(i, VARIABLE_PAUSE)
                else vc.getSMVVariable(i, VARIABLE_PAUSE).not()
                inputExpr.put(VARIABLE_PAUSE, pexpr)
            }

    }

    fun constraintOf(v: ProgramVariable): SMVExpr? {
        val name = v.name
        return inputExpr[name] ?: outputExpr[name]
    }

    override fun clone(): TableNode = copy().also { it.duration = duration; it.id = id }
}
