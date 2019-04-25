package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.TimeType
import edu.kit.iti.formal.automation.datatypes.values.TimeData
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.ast.BooleanLit.Companion.LFALSE
import edu.kit.iti.formal.automation.st.ast.BooleanLit.Companion.LTRUE
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import java.util.concurrent.Callable

class TranslationSfcToSt(index: Int = 0,
                         name: String = "",
                         network: SFCNetwork,
                         scope: Scope,
                         finalScan: Boolean = false,
                         sfcFlags: Boolean = false)
    : Callable<StatementList> {

    val pipelineData = PipelineData(index, name, network, scope, finalScan, sfcFlags)
    val pipelineSteps: List<PipelineStep>


    init {
        pipelineSteps = mutableListOf(
                this::assignStepVariables as PipelineStep,
                this::processTransitions as PipelineStep,
                ControlActions(),
                this::runActions as PipelineStep
        )

        if (sfcFlags) {
            pipelineSteps += SfcFlagIntroduction()
            scope.variables.forEach {
                pipelineData.resetStatements += SymbolicReference(it.name) assignTo it.init
            }
        }
    }

    override fun call(): StatementList {
        pipelineSteps.forEach { it(pipelineData) }
        return pipelineData.stBody
    }

    fun assignStepVariables(data: PipelineData) {
        data.run {
            IEC61131Facade.resolveDataTypes(BuiltinLoader.loadDefault(), scope)
            network.steps.forEach {
                val varName = data.stepName(it.name, index)
                if (!scope.variables.contains(varName)) {
                    val xtvar = VariableDeclaration(varName, scope.resolveDataType("xt"))
                    scope.variables.add(xtvar)
                    if (it.isInitial) {
                        val m: MutableMap<String, Initialization> = mutableMapOf("x" to LTRUE)
                        xtvar.typeDeclaration = StructureTypeDeclaration("XT",
                                initialization = StructureInitialization(m))
                    }
                }
            }
        }
    }

    fun processTransitions(data: PipelineData) {
        data.run {
            transitions.forEach { transition ->
                val ifBranches = mutableListOf<GuardedStatement>()
                transition.value.forEach {
                    val guard = ExpressionList(mutableListOf(it.guard))
                    if (index > 0) {
                        AstMutableVisitorWithReplacedStepNames(data).visit(guard)
                    }
                    var transitionIf = guard.first()
                    val ifAssignments = StatementList()
                    it.from.forEach { step ->
                        transitionIf = subRef(stepName(step.name, index), "X") and transitionIf
                        ifAssignments += (stepName(step.name, index).assignTo("_X", BooleanLit(false)))
                    }
                    it.to.forEach { step ->
                        ifAssignments += stepName(step.name).assignTo("_X", BooleanLit(true))
                        ifAssignments += stepName(step.name).assignTo("_T", TimeLit(TimeData()))
                    }
                    ifBranches.add(GuardedStatement(transitionIf, ifAssignments))
                }
                stBody.add(IfStatement(ifBranches))
            }
            assignAndReset()
        }
    }

    fun runActions(data: PipelineData) {
        data.run {
            actions.keys.forEach {
                val actionQ = SymbolicReference(it + "_Q")
                if (scope.hasVariable(it)) {
                    stBody.add(it assignTo actionQ)
                } else {
                    stBody.add(Statements.ifthen(actionQ, InvocationStatement(SymbolicReference(it))))
                }
                stBody.add(actionQ assignTo LFALSE)
            }
            network.steps.forEach {
                val varName = stepName(it.name)
                val addition = varName.assignTo("T", subRef(varName, "T") plus SymbolicReference("CYCLE_TIME"))
                stBody.add(Statements.ifthen(subRef(varName, "X"), addition))
            }
        }
    }


    class ControlActions : PipelineStep {
        val handlers = listOf<ActionQualifierHandler>(
                DelayedAndStored,
                NonStored,
                SetHandler,
                TimeLimited,
                TimeDelayed,
                Pulse,
                StoreAndDelay,
                StoreAndLimited)

        val secondaryHandler = listOf(Raising, Falling)


        override operator fun invoke(data: PipelineData) {
            data.createTimeVars()
            data.buildActionControl()
        }

        fun PipelineData.createTimeVars() {
            actions.forEach {
                if (it.value.actionBlockPairs.fold(false) { acc, pair ->
                            acc || pair.first.hasTime()
                        }) {
                    val actionT = it.key + "_T"
                    addToScope(actionT, TimeType.TIME_TYPE)
                    val ifBranches = mutableListOf<GuardedStatement>()
                    it.value.actionBlockPairs.filter { maybeTimedActionBlockPair ->
                        maybeTimedActionBlockPair.first.hasTime()
                    }.forEach { timedActionBlockPair ->
                        ifBranches.add(GuardedStatement(subRef(timedActionBlockPair.second, "X"),
                                StatementList(actionT assignTo timedActionBlockPair.first.time)))
                    }
                    stBody.add(IfStatement(ifBranches))
                }
            }
        }

        fun PipelineData.buildActionControl() {
            actions.forEach {
                val (name, info) = it
                val actionQ = info.actionQ
                scope.variables.add(VariableDeclaration(actionQ, AnyBit.BOOL))

                val stepsInQualifiers = it.value.actionStepsInQualifiers

                stepsInQualifiers.forEach { (qualifier, steps) ->
                    for (handler in handlers) {
                        if (qualifier == handler.qualifier) {
                            handler(it.value, steps, this)
                        }
                    }
                }

                if (finalScan) {
                    if (stepsInQualifiers.contains(OVERRIDING_RESET)) {
                        andedNotAssign(SymbolicReference(actionQ), it.value.resetExpr)
                    }
                    val trigName = name + "_Q_TRIG"
                    moduleFTRIG(trigName, SymbolicReference(actionQ))
                    oredAssign(SymbolicReference(actionQ), subRef(trigName, "Q"))
                }

                stepsInQualifiers.forEach { (qualifier, steps) ->
                    for (handler in secondaryHandler) {
                        if (qualifier == handler.qualifier) {
                            handler(it.value, steps, this)
                        }
                    }
                }

                if (!finalScan && stepsInQualifiers.contains(OVERRIDING_RESET)) {
                    andedNotAssign(SymbolicReference(actionQ), it.value.resetExpr)
                }
            }
        }
    }

    class SfcFlagIntroduction : PipelineStep {

        val SUPPORTED_SFC_FLAGS: MutableList<String> = mutableListOf()

        val SFC_INIT = createFlag("SFCInit")
        val SFC_RESET = createFlag("SFCReset")
        val SFC_PAUSE = createFlag("SFCPause")

        private fun createFlag(s: String): SymbolicReference = SymbolicReference(s).also {
            SUPPORTED_SFC_FLAGS += s
        }

        override fun invoke(data: PipelineData) {
            val newSt = StatementList()
            val ifAssignments = data.resetStatements
            data.addToScope(SUPPORTED_SFC_FLAGS, AnyBit.BOOL)
            newSt.add(IfStatement(
                    mutableListOf(GuardedStatement(SFC_INIT or SFC_RESET, ifAssignments))))

            newSt.add(IfStatement(mutableListOf(GuardedStatement(
                    !(SFC_INIT or SFC_PAUSE), data.stBody))))
            data.stBody = newSt
        }
    }

}

private fun stepsWithThisActionBlock(stepNames: Collection<String>) = stepNames.mapRef().chainORs()

private fun Collection<String>.mapRef(sub: String = "X"): List<Expression> {
    return map { name -> subRef(name, sub) }
}

private fun List<Expression>.chainORs(): Expression {
    return reduce { acc, s -> acc or s }
}

private infix fun SymbolicReference.assignTo(init: Expression?): Statement = AssignmentStatement(this, init!!)

private fun subRef(name: String, sub: String) = SymbolicReference(name, SymbolicReference(sub))

private infix fun String.assignTo(expr: Expression) =
        AssignmentStatement(SymbolicReference(this), expr)

private fun String.assignTo(sub: String, expr: Expression) =
        AssignmentStatement(subRef(this, sub), expr)

private fun String.assignSubTo(sub: String) =
        AssignmentStatement(subRef(this, sub), subRef(this, '_' + sub))

private class AstMutableVisitorWithReplacedStepNames(val data: PipelineData) : AstMutableVisitor() {
    override fun visit(symbolicReference: SymbolicReference): Expression {
        for (i in 0 until data.network.steps.size) {
            if (symbolicReference.identifier == data.network.steps[i].name) {
                symbolicReference.identifier = data.stepName(data.network.steps[i].name, i)
                break
            }
        }
        return super.visit(symbolicReference) as SymbolicReference
    }
}

/**object StepType {
enum class Type {
XT,
XINIT
}

private fun addStepType(typeName: Type, content: List<VariableDeclaration>, scope: Scope) {
val typeAsString = this.toLowerCaseString(typeName)
if (!scope.dataTypes.containsKey(typeAsString)) {
scope.dataTypes.register(typeAsString, StructureTypeDeclaration(typeAsString, content))
}
}

fun stepTypeInformation(scope: Scope, types: List<Type> = listOf(Type.XT, Type.XINIT)) {
types.forEach {
when (it) {
Type.XT -> addStepType(it, listOf(VariableDeclaration("X", AnyBit.BOOL), VariableDeclaration(
"_X", AnyBit.BOOL), VariableDeclaration("T", TimeType.TIME_TYPE),
VariableDeclaration("_T", TimeType.TIME_TYPE)), scope)
Type.XINIT -> addStepType(it, listOf(VariableDeclaration("X", 8, SimpleTypeDeclaration(
"", RefTo(), BooleanLit(true))), VariableDeclaration("_X", AnyBit.BOOL),
VariableDeclaration("T", TimeType.TIME_TYPE), VariableDeclaration("_T",
TimeType.TIME_TYPE)), scope)
}
}
}

fun toLowerCaseString(typeName: StepType.Type): String {
return typeName.toString().toLowerCase()
}
}*/


abstract class ActionQualifierHandler(val qualifier: SFCActionQualifier.Qualifier) {
    abstract operator fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData)
}

object DelayedAndStored : ActionQualifierHandler(DELAYED_AND_STORED) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val tonName = "${actionInfo.step}_DS_TMR"
        val rsName = "${actionInfo.step}_DS_FF"
        data.run {
            moduleTON(tonName, stepsWithThisActionBlock(steps),
                    SymbolicReference(actionInfo.actionT))
            moduleRS(rsName, subRef(tonName, "Q"), actionInfo.resetExpr)
            oredAssign(SymbolicReference(actionInfo.actionQ), subRef(tonName, "Q"))
        }
    }

}

object NonStored : ActionQualifierHandler(NON_STORED) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        data.stBody.add(actionInfo.actionQ assignTo stepsWithThisActionBlock(steps))
    }
}

object SetHandler : ActionQualifierHandler(SET) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val rsName = "${actionInfo.step}_S_FF"
        data.moduleRS(rsName, stepsWithThisActionBlock(steps), actionInfo.resetExpr)
        data.oredAssign(SymbolicReference(actionInfo.actionQ), subRef(rsName, "Q1"))
    }
}

object TimeLimited : ActionQualifierHandler(TIME_LIMITED) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val tonName = actionInfo.step + "_L_TMR"
        val stepsL = stepsWithThisActionBlock(steps)
        data.moduleTON(tonName, stepsL, SymbolicReference(actionInfo.actionT))
        data.oredAndNotAssign(SymbolicReference(actionInfo.actionQ), stepsL, subRef(tonName, "Q"))
    }
}

object TimeDelayed : ActionQualifierHandler(STORE_DELAYED) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val tonName = actionInfo.step + "_D_TMR"
        data.moduleTON(tonName, stepsWithThisActionBlock(steps), SymbolicReference(actionInfo.actionT))
        data.oredAssign(SymbolicReference(actionInfo.actionQ), subRef(tonName, "Q"))
    }

}

object Pulse : ActionQualifierHandler(PULSE) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val trigName = actionInfo.step + "_P_TRIG"
        data.moduleRTRIG(trigName, stepsWithThisActionBlock(steps))
        data.oredAssign(SymbolicReference(actionInfo.actionQ), subRef(trigName, "Q"))
    }
}

object StoreAndDelay : ActionQualifierHandler(STORE_AND_DELAY) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val rsName = actionInfo.step + "_SD_FF"
        val tonName = actionInfo.step + "_SD_TMR"
        data.moduleRS(rsName, stepsWithThisActionBlock(steps), actionInfo.resetExpr)
        data.moduleTON(tonName, subRef(rsName, "Q1"), SymbolicReference(actionInfo.actionT))
        data.oredAssign(SymbolicReference(actionInfo.actionQ), subRef(tonName, "Q"))
    }
}

object StoreAndLimited : ActionQualifierHandler(STORE_AND_LIMITED) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val rsName = actionInfo.step + "_SL_FF"
        val tonName = actionInfo.step + "_SL_TMR"
        val rsQ = subRef(rsName, "Q1")
        data.moduleRS(rsName, stepsWithThisActionBlock(steps),
                actionInfo.resetExpr)
        data.moduleTON(tonName, rsQ, SymbolicReference(actionInfo.actionT))
        data.oredAndNotAssign(SymbolicReference(actionInfo.actionQ), rsQ, subRef(tonName, "Q"))
    }
}


object Raising : ActionQualifierHandler(RAISING) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val trigName = actionInfo.step + "_P1_TRIG"
        data.moduleRTRIG(trigName, stepsWithThisActionBlock(steps))
        data.oredAssign(SymbolicReference(actionInfo.actionQ), subRef(trigName, "Q"))
    }
}

object Falling : ActionQualifierHandler(FALLING) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val trigName = actionInfo.step + "_P0_TRIG"
        data.moduleFTRIG(trigName, stepsWithThisActionBlock(steps))
        data.oredAssign(SymbolicReference(actionInfo.actionQ), subRef(trigName, "Q"))
    }
}


data class PipelineData(val index: Int = 0, val name : String,
                        val network: SFCNetwork,
                        val scope: Scope,
                        val finalScan: Boolean = false,
                        val sfcFlags: Boolean = false) {
    val transitions: Map<MutableSet<SFCStep>, List<SFCTransition>>
    var actions: MutableMap<String, ActionInfo> = mutableMapOf()
    val resetStatements: StatementList = StatementList()
    var stBody = StatementList()

    init {
        transitions = network.steps
                .flatMap { it.outgoing }
                .distinct()
                .sortedByDescending { it.priority }
                .groupBy { it.from }


        network.steps.forEach { step ->
            step.events.forEach {
                val qualifier = it.qualifier ?: SFCActionQualifier(NON_STORED)
                val name = stepName(step.name, index)
                if (actions.containsKey(it.actionName)) {
                    actions.getValue(it.actionName).addActionBlock(qualifier, name)
                } else {
                    actions[it.actionName] = ActionInfo(qualifier, name)
                }
            }
        }
    }


    fun stepName(stepName: String, idx: Int = index, sfcName: String = name): String {
        return if (idx > 0) {
            "${sfcName}_${idx}_${stepName}"
        } else {
            "${sfcName}_${stepName}"
        }
    }

    fun addToScope(name: String, type: AnyDt) {
        if (!scope.variables.contains(name)) {
            scope.variables.add(VariableDeclaration(name, type))
        }
    }

    fun addToScope(names: List<String>, type: AnyDt) {
        names.forEach { addToScope(it, type) }
    }

    fun assignAndReset() {
        network.steps.forEach {
            val varName = stepName(it.name, index)
            stBody.add(varName.assignSubTo("X"))
            stBody.add(varName.assignSubTo("T"))
            stBody.add(varName.assignTo("_X", BooleanLit(false)))
            stBody.add(varName.assignTo("_T", TimeLit(TimeData())))
        }
    }


    fun moduleFTRIG(name: String, clk: Expression) {
        moduleFB(name, "F_TRIG", listOf(Pair("CLK", clk)))
    }

    fun moduleRTRIG(name: String, clk: Expression) {
        moduleFB(name, "R_TRIG", listOf(Pair("CLK", clk)))
    }

    fun moduleTON(name: String, input: Expression, pt: Expression) {
        //$name(IN:=FALSE, PT:=T#0ms)
        resetStatements += InvocationStatement(SymbolicReference(name),
                mutableListOf(InvocationParameter("IN", false, LFALSE),
                        InvocationParameter("PT", false, TimeLit(TimeData()))))

        moduleFB(name, "TON", listOf(Pair("IN", input), Pair("PT", pt)))
    }

    fun moduleRS(name: String, set: Expression, reset1: Expression) {
        // $name(R:=TRUE);
        resetStatements += InvocationStatement(SymbolicReference(name),
                mutableListOf(InvocationParameter("R", false, LTRUE)))

        moduleFB(name, "RS", listOf(Pair("SET", set), Pair("RESET1", reset1)))
    }

    private fun moduleFB(name: String, type: String, parameters: List<Pair<String, Expression>>) {
        scope.variables.add(VariableDeclaration(name, SimpleTypeDeclaration("ANONYM", RefTo(type),
                null)))
        stBody.add(InvocationStatement(SymbolicReference(name), parameters.map { (left, right) ->
            InvocationParameter(left,
                    false, right)
        }.toMutableList()))
    }

    fun oredAssign(left: SymbolicReference, right: Expression) {
        stBody.add(AssignmentStatement(left, left or right))
    }

    fun oredAndNotAssign(left: SymbolicReference, center: Expression, right: Expression) {
        oredAssign(left, center and UnaryExpression(Operators.NOT, right))
    }

    fun andedNotAssign(left: SymbolicReference, right: Expression) {
        stBody.add(AssignmentStatement(left, left and UnaryExpression(Operators.NOT, right)))
    }
}

interface PipelineStep {
    operator fun invoke(data: PipelineData)
}


class ActionInfo(sfcActionQualifier: SFCActionQualifier, val step: String) {
    var actionBlockPairs: MutableList<Pair<SFCActionQualifier, String>> = mutableListOf()
    var actionStepsInQualifiers: MutableMap<SFCActionQualifier.Qualifier, MutableSet<String>> = mutableMapOf()

    val actionQ = "${step}_Q"
    val actionT = "${step}_T"

    val resetExpr by lazy {
        (actionStepsInQualifiers[OVERRIDING_RESET]?.mapRef() ?: listOf(LFALSE)).chainORs()
    }

    init {
        addActionBlock(sfcActionQualifier, step)
    }

    fun addActionBlock(sfcActionQualifier: SFCActionQualifier, step: String) {
        actionBlockPairs.add(Pair(sfcActionQualifier, step))
        if (actionStepsInQualifiers.contains(sfcActionQualifier.qualifier)) {
            actionStepsInQualifiers.getValue(sfcActionQualifier.qualifier).add(step)
        } else {
            actionStepsInQualifiers[sfcActionQualifier.qualifier] = mutableSetOf(step)
        }
    }
}