package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.TimeType
import edu.kit.iti.formal.automation.datatypes.values.*
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.ast.BooleanLit.Companion.LFALSE
import edu.kit.iti.formal.automation.st.ast.BooleanLit.Companion.LTRUE
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import org.antlr.v4.runtime.CommonToken
import java.math.BigDecimal
import java.math.BigInteger
import java.util.concurrent.Callable

class TranslationSfcToSt(network: SFCNetwork, name: String = "", index: Int = 0, scope: Scope, tokens: Int = 0,
                         finalScan: Boolean = true, sfcFlags: Boolean = true): Callable<StatementList> {

    private val pipelineData = PipelineData(network, name, index, scope, tokens, finalScan, sfcFlags)
    private val pipelineSteps: MutableList<PipelineStep>

    init {
        pipelineSteps = mutableListOf(AssignStepVariables)
        if (tokens == 1) enumForNoParallelismOptimizationInit()
        pipelineSteps.addAll(listOf(ProcessTransitions, ControlActions(), RunActions))
        if (sfcFlags) sfcFlagsInit()
    }

    override fun call() = pipelineData.stBody.also { pipelineSteps.forEach { it.invoke(pipelineData) } }

    private fun enumForNoParallelismOptimizationInit() {
        pipelineSteps.addAll(listOf(AssignEnumVariable, SetActiveStepFromEnum))
        pipelineData.run {
            val enumType = EnumerationTypeDeclaration(enumName)
            for (step in network.steps)
                enumType.addValue(CommonToken(IEC61131Lexer.IDENTIFIER, enumStepName(stepName(step.name))))
            enumType.initialization = IdentifierInitializer(value = enumStepName(network.initialStep!!.name))
            scope.dataTypes.register(enumName, enumType)
            resetStatements += enumName.assignTo(enumType.initialization!!.value!!)
        }
    }

    private fun sfcFlagsInit() {
        val sfcFlagIntroduction = SfcFlagIntroduction()
        pipelineSteps += sfcFlagIntroduction
        pipelineData.run {
            scope.variables.filter{ !sfcFlagIntroduction.supportedSfcFlags.contains(it.name) }.forEach {
                if (it.init != null) {
                    if ((it.clone().init!!.getValue().value as? RecordValue)?.fieldValues?.get("X")?.value == true)
                        resetStatements += it.name.assignTo("X", LTRUE)
                    else resetStatements += SymbolicReference(it.name) assignTo it.init
                } else if (it.initValue != null) {
                    val (type, _) = it.initValue as Value<*, *>
                    val defaultVal: Expression = when (type.name) {
                        "BOOL" -> LFALSE
                        "SINT", "INT", "DINT", "LINT", "USINT", "UINT", "UDINT", "ULINT" ->
                            IntegerLit(value = BigInteger.valueOf(0))
                        "REAL", "LREAL" -> RealLit(value = BigDecimal.valueOf(0))
                        "TIME", "LTIME" -> TimeLit(TimeData())
                        "DATE", "LDATE" -> DateLit(DateData(1970))
                        "TIME_OF_DAY", "TOD", "LTIME_OF_DAY", "LTOD" -> ToDLit(TimeofDayData())
                        "DATE_AND_TIME", "DT", "LDATE_AND_TIME", "LDT" ->
                            DateAndTimeLit(DateAndTimeData(DateData(1970), TimeofDayData()))
                        "STRING", "WSTRING" -> StringLit(value = "")
                        "CHAR", "WCHAR", "BYTE", "WORD", "DWORD", "LWORD" -> BitLit(value = 0)
                        else -> UnindentifiedLit("0")
                    }
                    resetStatements += SymbolicReference(it.name) assignTo defaultVal
                }
            }
        }
    }

    object AssignStepVariables: PipelineStep {
        override operator fun invoke(data: PipelineData) {
            data.run {
                IEC61131Facade.resolveDataTypes(BuiltinLoader.loadDefault(), scope)
                network.steps.forEach {
                    val varName = stepName(it.name)
                    val xtVar = VariableDeclaration(varName, scope.resolveDataType("xt"))
                    if (tokens != 1) {
                        if (it.isInitial) {
                            val m: MutableMap<String, Initialization> = mutableMapOf("X" to LTRUE)
                            xtVar.typeDeclaration = StructureTypeDeclaration("xt",
                                    initialization = StructureInitialization(m))
                            resetStatements += varName.assignTo("X", LTRUE)
                        } else resetStatements += varName.assignTo("X", LFALSE)
                        resetStatements += varName.assignTo("T", TimeLit(TimeData()))
                    }
                    scope.variables.add(xtVar)
                }
            }
        }
    }

    object AssignEnumVariable: PipelineStep {
        override operator fun invoke(data: PipelineData) {
            data.run {scope.variables.add(VariableDeclaration(enumName, scope.resolveDataType(enumName)))}
        }
    }

    object SetActiveStepFromEnum: PipelineStep {
        override operator fun invoke(data: PipelineData) {
            data.run {
                val enum = scope.getVariable(enumName)!!.name
                val ifBranches = mutableListOf<GuardedStatement>()
                network.steps.forEach {
                    val step = stepName(it.name)
                    val enumStep = enumStepName(step)
                    ifBranches.add(GuardedStatement(SymbolicReference(enum).eq(SymbolicReference(enumStep)),
                            StatementList(step.assignTo("X", LTRUE))))
                }
                stBody.add(IfStatement(ifBranches))
            }
        }
    }

    object ProcessTransitions: PipelineStep {
        override operator fun invoke(data: PipelineData) {
            data.run {
                initializeTemps()
                val ifBranches = mutableListOf<GuardedStatement>()
                transitions.forEach { transition ->
                    transition.value.forEach {
                        val guard = ExpressionList(mutableListOf(it.guard))
                        if (index > 0) AstMutableVisitorWithReplacedStepNames(this).visit(guard)
                        var transitionIf = guard.first()
                        val ifAssignments = StatementList()
                        it.from.forEach { step ->
                            val stepName = stepName(step.name)
                            transitionIf = subRef(stepName, "X") and transitionIf
                            ifAssignments += (stepName.assignTo("_X", LFALSE))
                        }
                        it.to.forEach { step ->
                            val stepName = stepName(step.name)
                            ifAssignments += stepName.assignTo("_X", LTRUE)
                            ifAssignments += stepName.assignTo("_T", TimeLit(TimeData()))
                        }
                        ifBranches.add(GuardedStatement(transitionIf, ifAssignments))
                    }
                    if (tokens != 1) {
                        stBody.add(IfStatement(ifBranches.toMutableList()))
                        ifBranches.clear()
                    }
                }
                if (tokens == 1) stBody.add(IfStatement(ifBranches))
                assignAndReset()
            }
        }
    }

    class ControlActions: PipelineStep {
        private val handlers = listOf(NonStored, SetHandler, TimeLimited, TimeDelayed, Pulse, StoreAndDelay,
                DelayedAndStored, StoreAndLimited)
        private val secondaryHandlers = listOf(Rising, Falling)

        override operator fun invoke(data: PipelineData) {
            data.run {
                createTimeVars()
                buildActionControl()
            }
        }

        private fun PipelineData.createTimeVars() {
            actions.forEach {
                if (it.value.actionBlockPairs.fold(false) { acc, pair -> acc || pair.first.hasTime() }) {
                    val actionT = "${it.key}_T"
                    addToScope(actionT, TimeType.TIME_TYPE)
                    val ifBranches = mutableListOf<GuardedStatement>()
                    it.value.actionBlockPairs.filter { maybeTimedActionBlockPair ->
                        maybeTimedActionBlockPair.first.hasTime() }.forEach { timedActionBlockPair ->
                        ifBranches.add(GuardedStatement(subRef(timedActionBlockPair.second, "X"),
                                StatementList(actionT assignTo timedActionBlockPair.first.time)))
                    }
                    resetStatements += actionT.assignTo(TimeLit(TimeData()))
                    stBody.add(IfStatement(ifBranches))
                }
            }
        }

        private fun PipelineData.buildActionControl() {
            actions.forEach {
                val (name, info) = it
                val actionQ = info.actionQ
                scope.variables.add(VariableDeclaration(actionQ, AnyBit.BOOL))
                val stepsInQualifiers = it.value.actionStepsInQualifiers
                var iecStep = false
                for (handler in handlers) {
                    stepsInQualifiers.forEach { (qualifier, steps) ->
                        if (qualifier == handler.qualifier) {
                            handler(it.value, steps, this)
                            iecStep = true
                        }
                    }
                }
                val optimizableMainAction: ActionQualifierHandler
                if (iecStep) {
                    if (finalScan) {
                        if (stepsInQualifiers.contains(OVERRIDING_RESET))
                            andedNotAssign(SymbolicReference(actionQ), it.value.resetExpr)
                        val trigName = "${name}_TRIG"
                        moduleTRIG(trigName, SymbolicReference(actionQ), "F_TRIG")
                        oredAssign(SymbolicReference(actionQ), subRef(trigName, "Q"))
                    }
                    optimizableMainAction = MainAction
                } else optimizableMainAction = SimpleMainAction
                stepsInQualifiers.forEach { (qualifier, steps) ->
                    if (qualifier == MAIN_ACTION) optimizableMainAction(it.value, steps, this)
                }
                for (handler in secondaryHandlers) {
                    stepsInQualifiers.forEach { (qualifier, steps) ->
                        if (qualifier == handler.qualifier) handler(it.value, steps, this)
                    }
                }
                if (!finalScan && stepsInQualifiers.contains(OVERRIDING_RESET))
                    andedNotAssign(SymbolicReference(actionQ), it.value.resetExpr)
            }
        }
    }

    object RunActions: PipelineStep {
        override operator fun invoke(data: PipelineData) {
            data.run {
                actions.keys.forEach {
                    val actionQ = SymbolicReference(actions[it]!!.actionQ)
                    val name = actions[it]!!.originalName
                    if (scope.hasVariable(name)) stBody.add(it assignTo actionQ)
                    else stBody.add(Statements.ifthen(actionQ, InvocationStatement(SymbolicReference(name))))
                    stBody.add(actionQ assignTo LFALSE)
                }
                val ifBranches = mutableListOf<GuardedStatement>()
                network.steps.forEach {
                    val varName = stepName(it.name)
                    val addition = varName.assignTo("T",
                            subRef(varName, "T") plus SymbolicReference("CYCLE_TIME"))
                    if (tokens == 1) ifBranches.add(GuardedStatement(subRef(varName, "X"),
                            StatementList(enumName.assignTo(varName), varName.assignTo("X", LFALSE), addition)))
                    else stBody.add(Statements.ifthen(subRef(varName, "X"), addition))
                }
                if (tokens == 1) stBody.add(IfStatement(ifBranches))
            }
        }
    }

    class SfcFlagIntroduction: PipelineStep {
        val supportedSfcFlags: MutableList<String> = mutableListOf()
        private val sfcInit = createFlag("SFCInit")
        private val sfcReset = createFlag("SFCReset")
        private val sfcPause = createFlag("SFCPause")

        private fun createFlag(s: String): SymbolicReference = SymbolicReference(s).also { supportedSfcFlags += s }

        override fun invoke(data: PipelineData) {
            data.run {
                val newSt = StatementList()
                addToScope(supportedSfcFlags, AnyBit.BOOL)
                newSt.add(IfStatement(mutableListOf(GuardedStatement(sfcInit or sfcReset, resetStatements))))
                newSt.add(IfStatement(mutableListOf(GuardedStatement(!(sfcInit or sfcPause), stBody.clone()))))
                stBody.clear()
                stBody.add(newSt)
            }
        }
    }
}

private fun stepsWithThisActionBlock(stepNames: Collection<String>) = stepNames.mapRef().chainORs()

private fun Collection<String>.mapRef(sub: String = "X"): List<Expression> { return map { name -> subRef(name, sub) } }

private fun List<Expression>.chainORs(): Expression { return reduce { acc, s -> acc or s } }

private infix fun SymbolicReference.assignTo(init: Expression?): Statement = AssignmentStatement(this, init!!)

private fun subRef(name: String, sub: String) = SymbolicReference(name, SymbolicReference(sub))

private infix fun String.assignTo(expr: Expression) = AssignmentStatement(SymbolicReference(this), expr)

private infix fun String.assignTo(expr: String) =
        AssignmentStatement(SymbolicReference(this), SymbolicReference(expr))

private fun String.assignTo(sub: String, expr: Expression) = AssignmentStatement(subRef(this, sub), expr)

private fun String.assignSubTo(sub: String) = assignSubTo(sub, "_$sub")

private fun String.assignSubTo(sub: String, other: String) =
        AssignmentStatement(subRef(this, sub), subRef(this, other))

private class AstMutableVisitorWithReplacedStepNames(val data: PipelineData): AstMutableVisitor() {
    override fun visit(symbolicReference: SymbolicReference): Expression {
        data.run {
            for (i in 0 until network.steps.size) {
                if (symbolicReference.identifier == network.steps[i].name)
                    symbolicReference.identifier = stepName(network.steps[i].name); break
            }
        }
        return super.visit(symbolicReference) as SymbolicReference
    }
}

abstract class ActionQualifierHandler(val qualifier: SFCActionQualifier.Qualifier) {
    abstract operator fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData)
}

object NonStored: ActionQualifierHandler(NON_STORED) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        data.stBody.add(actionInfo.actionQ assignTo stepsWithThisActionBlock(steps))
    }
}

object MainAction: ActionQualifierHandler(MAIN_ACTION) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        data.oredAssign(SymbolicReference(actionInfo.actionQ), stepsWithThisActionBlock(steps))
    }
}

object SimpleMainAction: ActionQualifierHandler(MAIN_ACTION) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) =
            NonStored.invoke(actionInfo, steps, data)
}

object SetHandler: ActionQualifierHandler(SET) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val rsName = "${actionInfo.name}_S_FF"
        data.run {
            moduleRS(rsName, stepsWithThisActionBlock(steps), actionInfo.resetExpr)
            oredAssign(SymbolicReference(actionInfo.actionQ), subRef(rsName, "Q1"))
        }
    }
}

object TimeLimited: ActionQualifierHandler(TIME_LIMITED) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val tonName = "${actionInfo.name}_L_TMR"
        val stepsL = stepsWithThisActionBlock(steps)
        data.run {
            moduleTON(tonName, stepsL, SymbolicReference(actionInfo.actionT))
            oredAndNotAssign(SymbolicReference(actionInfo.actionQ), stepsL, subRef(tonName, "Q"))
        }
    }
}

object TimeDelayed: ActionQualifierHandler(STORE_DELAYED) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val tonName = "${actionInfo.name}_D_TMR"
        data.run {
            moduleTON(tonName, stepsWithThisActionBlock(steps), SymbolicReference(actionInfo.actionT))
            oredAssign(SymbolicReference(actionInfo.actionQ), subRef(tonName, "Q"))
        }
    }
}

object Pulse: ActionQualifierHandler(PULSE) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val trigName = "${actionInfo.name}_P_TRIG"
        data.run {
            moduleTRIG(trigName, stepsWithThisActionBlock(steps))
            oredAssign(SymbolicReference(actionInfo.actionQ), subRef(trigName, "Q"))
        }
    }
}

object StoreAndDelay: ActionQualifierHandler(STORE_AND_DELAY) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val rsName = "${actionInfo.name}_SD_FF"
        val tonName = "${actionInfo.name}_SD_TMR"
        data.run {
            moduleRS(rsName, stepsWithThisActionBlock(steps), actionInfo.resetExpr)
            moduleTON(tonName, subRef(rsName, "Q1"), SymbolicReference(actionInfo.actionT))
            oredAssign(SymbolicReference(actionInfo.actionQ), subRef(tonName, "Q"))
        }
    }
}

object DelayedAndStored: ActionQualifierHandler(DELAYED_AND_STORED) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val tonName = "${actionInfo.name}_DS_TMR"
        val rsName = "${actionInfo.name}_DS_FF"
        data.run {
            moduleTON(tonName, stepsWithThisActionBlock(steps), SymbolicReference(actionInfo.actionT))
            moduleRS(rsName, subRef(tonName, "Q"), actionInfo.resetExpr)
            oredAssign(SymbolicReference(actionInfo.actionQ), subRef(tonName, "Q"))
        }
    }
}

object StoreAndLimited: ActionQualifierHandler(STORE_AND_LIMITED) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val rsName = "${actionInfo.name}_SL_FF"
        val tonName = "${actionInfo.name}_SL_TMR"
        val rsQ = subRef(rsName, "Q1")
        data.run {
            moduleRS(rsName, stepsWithThisActionBlock(steps), actionInfo.resetExpr)
            moduleTON(tonName, rsQ, SymbolicReference(actionInfo.actionT))
            oredAndNotAssign(SymbolicReference(actionInfo.actionQ), rsQ, subRef(tonName, "Q"))
        }
    }
}

object Rising: ActionQualifierHandler(RAISING) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val trigName = "${actionInfo.name}_P1_TRIG"
        data.run {
            moduleTRIG(trigName, stepsWithThisActionBlock(steps))
            oredAssign(SymbolicReference(actionInfo.actionQ), subRef(trigName, "Q"))
        }
    }
}

object Falling: ActionQualifierHandler(FALLING) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val trigName = "${actionInfo.name}_P0_TRIG"
        data.run {
            moduleTRIG(trigName, stepsWithThisActionBlock(steps), "F_TRIG")
            oredAssign(SymbolicReference(actionInfo.actionQ), subRef(trigName, "Q"))
        }
    }
}

data class PipelineData(val network: SFCNetwork, val name: String, val index: Int, val scope: Scope, val tokens: Int,
                        val finalScan: Boolean, val sfcFlags: Boolean) {
    val transitions: Map<MutableSet<SFCStep>, List<SFCTransition>> = network.steps.flatMap { it.outgoing }.distinct()
            .sortedByDescending { it.priority }.groupBy { it.from }
    val actions: MutableMap<String, ActionInfo> = mutableMapOf()
    val resetStatements: StatementList = StatementList()
    val stBody = StatementList()
    val enumName = name + network.nodeName + index

    init {
        network.steps.forEach { step ->
            step.events.forEach {
                val qualifier = it.qualifier ?: SFCActionQualifier(NON_STORED)
                val stepName = stepName(step.name)
                val actionName = it.actionName.replace('.', '_')
                if (actions.containsKey(actionName))
                    actions.getValue(actionName).addActionBlock(qualifier, stepName)
                else actions[actionName] = ActionInfo(it.actionName, qualifier, stepName)
            }
        }
    }

    fun stepName(stepName: String, idx: Int = index, sfcName: String = name) = when (idx) {
        0 -> "$sfcName$stepName"
        else -> "$sfcName${idx}_$stepName"
    }

    fun enumStepName(stepName: String) = "Enum_$stepName"

    fun addToScope(name: String, type: AnyDt) {
        if (!scope.variables.contains(name)) scope.variables.add(VariableDeclaration(name, type))
    }

    fun addToScope(names: List<String>, type: AnyDt) { names.forEach { addToScope(it, type) } }

    fun initializeTemps() {
        network.steps.forEach {
            val varName = stepName(it.name)
            stBody.add(varName.assignSubTo("_X", "X"))
            stBody.add(varName.assignSubTo("_T", "T"))
        }
    }

    fun assignAndReset() {
        network.steps.forEach {
            val varName = stepName(it.name)
            stBody.add(varName.assignSubTo("X"))
            stBody.add(varName.assignSubTo("T"))
            stBody.add(varName.assignTo("_X", LFALSE))
            stBody.add(varName.assignTo("_T", TimeLit(TimeData())))
        }
    }

    fun moduleTON(name: String, input: Expression, pt: Expression) {
        resetStatements += InvocationStatement(SymbolicReference(name), mutableListOf(InvocationParameter("IN",
                false, LFALSE), InvocationParameter("PT", false, TimeLit(TimeData()))))
        moduleFB(name, "TON", listOf(Pair("IN", input), Pair("PT", pt)))
    }

    fun moduleRS(name: String, set: Expression, reset1: Expression) {
        resetStatements += InvocationStatement(SymbolicReference(name),
                mutableListOf(InvocationParameter("R", false, LTRUE)))
        moduleFB(name, "RS", listOf(Pair("SET", set), Pair("RESET1", reset1)))
    }

    fun moduleTRIG(name: String, clk: Expression, type: String = "R_TRIG") {
        resetStatements += InvocationStatement(SymbolicReference(name),
                mutableListOf(InvocationParameter("CLK", false, LFALSE)))
        moduleFB(name, type, listOf(Pair("CLK", clk)))
    }

    private fun moduleFB(name: String, type: String, parameters: List<Pair<String, Expression>>) {
        scope.variables.add(VariableDeclaration(name, SimpleTypeDeclaration(baseType = RefTo(type))))
        stBody.add(InvocationStatement(SymbolicReference(name), parameters.map { (left, right) ->
            InvocationParameter(left, false, right) }.toMutableList()))
    }

    fun oredAssign(left: SymbolicReference, right: Expression) {
        stBody.add(AssignmentStatement(left, left or right))
    }

    fun oredAndNotAssign(left: SymbolicReference, center: Expression, right: Expression) {
        oredAssign(left, center and !right)
    }

    fun andedNotAssign(left: SymbolicReference, right: Expression) {
        stBody.add(AssignmentStatement(left, left and !right))
    }
}

interface PipelineStep { operator fun invoke(data: PipelineData) }

class ActionInfo(var name: String, sfcActionQualifier: SFCActionQualifier, val step: String) {
    var actionBlockPairs: MutableList<Pair<SFCActionQualifier, String>> = mutableListOf()
    var actionStepsInQualifiers: MutableMap<SFCActionQualifier.Qualifier, MutableSet<String>> = mutableMapOf()

    val originalName = name
    val actionQ: String
    val actionT: String

    val resetExpr by lazy { (actionStepsInQualifiers[OVERRIDING_RESET]?.mapRef() ?: listOf(LFALSE)).chainORs() }

    init {
        name = name.replace('.', '_')
        actionQ = "${name}_Q"
        actionT = "${name}_T"
        addActionBlock(sfcActionQualifier, step)
    }

    fun addActionBlock(sfcActionQualifier: SFCActionQualifier, step: String) {
        actionBlockPairs.add(Pair(sfcActionQualifier, step))
        if (actionStepsInQualifiers.contains(sfcActionQualifier.qualifier))
            actionStepsInQualifiers.getValue(sfcActionQualifier.qualifier).add(step)
        else actionStepsInQualifiers[sfcActionQualifier.qualifier] = mutableSetOf(step)
    }
}
