/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.analysis.toHuman
import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.*
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.ast.BooleanLit.Companion.LFALSE
import edu.kit.iti.formal.automation.st.ast.BooleanLit.Companion.LTRUE
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import org.antlr.v4.runtime.CommonToken
import java.util.*
import java.util.concurrent.Callable

private val SFCStep.onEntry: String?
    get() = events.find { it.qualifier?.qualifier == RAISING }?.actionName

private val SFCStep.onExit: String?
    get() = events.find { it.qualifier?.qualifier == FALLING }?.actionName

private val SFCStep.onWhile: String?
    get() = (
        events.find { it.qualifier?.qualifier == WHILE }
            ?: events.find { it.qualifier?.qualifier == NON_STORED }
        )?.actionName

private val Scope.resetStatements: StatementList
    get() {
        val seq = StatementList()
        variables
            .filter { !it.isType(VD_EXCLUDE_RESET) } // for none SFC flags
            .forEach {
                val v = it.initValue
                    ?: throw IllegalStateException("value not set for variable declaration ${it.toHuman()}")
                val s = v.assignTo(SymbolicReference(it.name))
                if (s != null) {
                    seq.addAll(s)
                } else {
                    seq.comment("Do not know how to handle reset for: $it")
                }
            }
        return seq
    }

/**
 * Flag for VariableDeclaration#type to identify SFC flags.
 */
val VD_EXCLUDE_RESET = VariableDeclaration.FLAG_COUNTER.get()
val STRUCT_SFC_STEP_NAME = "SFC_STEPS"

/**
 * A step in the SFC pipeline.
 */
interface PipelineStep {
    /**
     * Performs the transformation by mutation of the given elements in data.
     */
    operator fun invoke(data: PipelineData)
}

/**
 * Class describes the maximal needed amount of tokens in an SFC.
 */
sealed class TokenAmount {
    object Unbounded : TokenAmount()
    class Bounded(val max: Int) : TokenAmount()
}

/**
 * Transformation pipeline from SFC implementation to ST Code.
 */
open class TranslationSfcToStPipeline(
    network: SFCNetwork,
    name: String,
    index: Int = 0,
    scope: Scope,
    finalScan: Boolean = true,
    sfcFlags: Boolean = true,
    maxNeededTokens: TokenAmount = TokenAmount.Unbounded,
) : Callable<StatementList> {

    val pipelineData = PipelineData(network, name, index, scope, finalScan, sfcFlags, maxNeededTokens)
    protected val pipelineSteps: MutableList<PipelineStep> = mutableListOf()

    init {
        // configures the pipeline if the maximal needed token is 1
        if (pipelineData.tokenIsBoundedTo1) {
            pipelineSteps += IntroduceStateEnumVariable
            pipelineSteps += AssignStepVariables
            pipelineSteps += SetActiveStepFromEnum
            pipelineSteps += ProcessTransitionsToken1
        } else {
            pipelineSteps += AssignStepVariables
            pipelineSteps += ProcessTransitions
        }
        pipelineSteps += ControlActions()
        pipelineSteps += RunActions
        pipelineSteps += IncreaseStepTime

        if (sfcFlags) {
            pipelineSteps += SfcFlagIntroduction
        }
    }

    override fun call(): StatementList {
        for (it in pipelineSteps) {
            pipelineData.stBody.comment("Running pipeline step: ${it.javaClass.name}")
            it.invoke(pipelineData)
            pipelineData.stBody.comment("End of: ${it.javaClass.name}")
        }
        return pipelineData.stBody
    }
}

/**
 *
 */
private object AssignStepVariables : PipelineStep {
    override operator fun invoke(data: PipelineData) {
        data.run {
            network.steps.forEach {
                val varName = stepName(it.name)
                val xtVar = VariableDeclaration(varName, structSfcStep)
                val v = RecordValue()
                v.fieldValues["X"] = if (it.isInitial) TRUE else FALSE
                xtVar.initValue = VStruct(structSfcStep, v)
                scope.variables.add(xtVar)
            }
        }
    }
}

private object IntroduceStateEnumVariable : PipelineStep {
    override operator fun invoke(data: PipelineData) {
        data.run {
            stateEnumTypeDeclaration
            val vd = VariableDeclaration(stateName.identifier, stateEnumType)
            vd.initValue = VAnyEnum(stateEnumType, enumStepName(stepName(network.initialStep!!.name)))
            scope.variables.add(vd)
        }
    }
}

/**
 * This pipeline step writes the assign `<stepName>.X = STATE = <stepName>`
 */
private object SetActiveStepFromEnum : PipelineStep {
    override operator fun invoke(data: PipelineData) {
        data.run {
            network.steps.forEach {
                val step = stepName(it.name)
                stBody.add(SymbolicReference(step)["X"] assignTo (stateName eq enumValue(it)))
            }
        }
    }
}

private object ProcessTransitions : PipelineStep {
    fun initializeTemps(data: PipelineData) {
        data.network.steps.forEach {
            val varName = data.stepName(it.name)
            data.stBody.add(varName.assignSubTo("_X", "X"))
            data.stBody.add(varName.assignSubTo("_T", "T"))
        }
    }

    fun assignAndReset(data: PipelineData) {
        data.network.steps.forEach {
            val varName = data.stepName(it.name)
            data.stBody.add(varName.assignSubTo("X"))
            data.stBody.add(varName.assignSubTo("T"))
            data.stBody.add(varName.assignTo("_X", LFALSE))
            data.stBody.add(varName.assignTo("_T", TimeLit(TimeData())))
        }
    }

    override operator fun invoke(data: PipelineData) {
        data.run {
            initializeTemps(data)
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
                stBody.add(IfStatement(ifBranches.toMutableList()))
                ifBranches.clear()
            }
            assignAndReset(data)
        }
    }
}

/**
 *
 */
private object ProcessTransitionsToken1 : PipelineStep {
    override operator fun invoke(data: PipelineData) {
        data.run {
            val cases = CaseStatement(SymbolicReference(enumName))
            stBody.add(cases)
            network.steps.forEach { step ->
                val stepState = enumStepName(stepName(step.name))
                val cc = CaseCondition.Enumeration(EnumLit(stateEnumType, stepState))
                val case = Case()
                val ifAssignments = IfStatement()
                case.statements.add(ifAssignments)
                case.addCondition(cc)
                cases.addCase(case)

                step.outgoing.forEach {
                    val guard = ExpressionList(mutableListOf(it.guard)).clone()

                    if (index > 0) {
                        AstMutableVisitorWithReplacedStepNames(this).visit(guard)
                    }

                    val cond = guard.chainAnd()
                    val stepName = (stepName(step.name))
                    val seq = StatementList()
                    // by assumption there is only one outgoing state
                    seq += stateName assignTo enumValue(it.to.first())
                    seq += stepName(it.to.first().name).assignTo("X", LTRUE)
                    seq += stepName.assignTo("T", TimeLit(TimeData()))
                    ifAssignments.addGuardedCommand(cond, seq)
                }
            }
        }
    }
}

private fun ExpressionList.chainAnd() = if (isEmpty()) LTRUE else reduce { a, b -> a and b }

private class ControlActions : PipelineStep {
    private val handlers = listOf(
        NonStored,
        SetHandler,
        TimeLimited,
        TimeDelayed,
        Pulse,
        StoreAndDelay,
        DelayedAndStored,
        StoreAndLimited,
    )
    private val secondaryHandlers = listOf(Rising, Falling)

    override operator fun invoke(data: PipelineData) {
        data.run {
            actions.forEach { t, u ->
                stBody.add(u.actionQ assignTo LFALSE)
            }
            createTimeVars()
            buildActionControl()
        }
    }

    private fun PipelineData.createTimeVars() {
        actions.forEach {
            val hasTime = it.value.actionBlockPairs.any { (q, id) -> q.hasTime() }
            if (hasTime) {
                val actionT = "${it.key}_T"
                addToScope(actionT, TimeType.TIME_TYPE).initValue = VTime(TimeType.TIME_TYPE, TimeData())
                val ifBranches = mutableListOf<GuardedStatement>()
                it.value.actionBlockPairs.filter { maybeTimedActionBlockPair ->
                    maybeTimedActionBlockPair.first.hasTime()
                }.forEach { timedActionBlockPair ->
                    ifBranches.add(
                        GuardedStatement(
                            subRef(timedActionBlockPair.second, "X"),
                            StatementList(actionT assignTo timedActionBlockPair.first.time),
                        ),
                    )
                }
                specialResetStatements += actionT.assignTo(TimeLit(TimeData()))
                stBody.add(IfStatement(ifBranches))
            }
        }
    }

    private fun PipelineData.buildActionControl() {
        actions.forEach {
            val (name, info) = it
            val actionQ = info.actionQ
            addToScope(actionQ, AnyBit.BOOL).initValue = FALSE
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
                    if (stepsInQualifiers.contains(OVERRIDING_RESET)) {
                        andedNotAssign(SymbolicReference(actionQ), it.value.resetExpr)
                    }
                    val trigName = "${name}_TRIG"
                    moduleTRIG(trigName, SymbolicReference(actionQ), "F_TRIG")
                    oredAssign(SymbolicReference(actionQ), subRef(trigName, "Q"))
                }
                optimizableMainAction = MainAction
            } else {
                optimizableMainAction = SimpleMainAction
            }
            stepsInQualifiers.forEach { (qualifier, steps) ->
                if (qualifier == WHILE) optimizableMainAction(it.value, steps, this)
            }
            for (handler in secondaryHandlers) {
                stepsInQualifiers.forEach { (qualifier, steps) ->
                    if (qualifier == handler.qualifier) handler(it.value, steps, this)
                }
            }
            if (!finalScan && stepsInQualifiers.contains(OVERRIDING_RESET)) {
                andedNotAssign(SymbolicReference(actionQ), it.value.resetExpr)
            }
        }
    }
}

private object RunActions : PipelineStep {
    override operator fun invoke(data: PipelineData) {
        data.run {
            actions.keys.forEach {
                val actionQ = SymbolicReference(actions[it]!!.actionQ)
                val name = actions[it]!!.originalName
                if (scope.hasVariable(name)) {
                    stBody.add(it assignTo actionQ)
                } else {
                    stBody.add(Statements.ifthen(actionQ, InvocationStatement(SymbolicReference(name))))
                }
            }
            // val ifBranches = mutableListOf<GuardedStatement>()
        }
    }
}

private object IncreaseStepTime : PipelineStep {
    override fun invoke(data: PipelineData) {
        data.run {
            network.steps.forEach {
                val varName = SymbolicReference(stepName(it.name))
                val addition = varName["T"] assignTo
                    (varName["T"] plus SymbolicReference("CYCLE_TIME"))
                stBody.add(Statements.ifthen(varName["X"], addition))
            }
        }
    }
}

private object SfcFlagIntroduction : PipelineStep {
    val supportedSfcFlags: MutableList<String> = mutableListOf()
    private val sfcInit = createFlag("SFCInit")
    private val sfcReset = createFlag("SFCReset")
    private val sfcPause = createFlag("SFCPause")

    private fun createFlag(s: String): SymbolicReference = SymbolicReference(s).also {
        supportedSfcFlags += s
    }

    override fun invoke(data: PipelineData) {
        data.run {
            val newSt = StatementList()
            addToScope(supportedSfcFlags, AnyBit.BOOL, type = VD_EXCLUDE_RESET)
            val seq = StatementList(scope.resetStatements + specialResetStatements)
            newSt.add(IfStatement(mutableListOf(GuardedStatement(sfcInit or sfcReset, seq))))
            newSt.add(IfStatement(mutableListOf(GuardedStatement(!(sfcInit or sfcPause), stBody))))
            stBody = newSt
        }
    }
}

private fun stepsWithThisActionBlock(stepNames: Collection<String>) = stepNames.mapRef().chainORs()

private fun Collection<String>.mapRef(sub: String = "X"): List<Expression> = map { name -> subRef(name, sub) }

private fun List<Expression>.chainORs(): Expression = reduce { acc, s -> acc or s }

private fun subRef(name: String, sub: String) = SymbolicReference(name, SymbolicReference(sub))

fun String.assignTo(sub: String, expr: Expression) = AssignmentStatement(subRef(this, sub), expr)

private fun String.assignSubTo(sub: String) = assignSubTo(sub, "_$sub")

private fun String.assignSubTo(sub: String, other: String) = AssignmentStatement(subRef(this, sub), subRef(this, other))

private class AstMutableVisitorWithReplacedStepNames(val data: PipelineData) : AstMutableVisitor() {
    override fun visit(symbolicReference: SymbolicReference): Expression {
        data.run {
            for (i in 0 until network.steps.size) {
                if (symbolicReference.identifier == network.steps[i].name) {
                    symbolicReference.identifier = stepName(network.steps[i].name)
                }
                break
            }
        }
        return super.visit(symbolicReference) as SymbolicReference
    }
}

abstract class ActionQualifierHandler(val qualifier: SFCActionQualifier.Qualifier) {
    abstract operator fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData)
}

object NonStored : ActionQualifierHandler(NON_STORED) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        data.stBody.add(actionInfo.actionQ assignTo stepsWithThisActionBlock(steps))
    }
}

object MainAction : ActionQualifierHandler(WHILE) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        data.oredAssign(SymbolicReference(actionInfo.actionQ), stepsWithThisActionBlock(steps))
    }
}

object SimpleMainAction : ActionQualifierHandler(WHILE) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) =
        NonStored.invoke(actionInfo, steps, data)
}

object SetHandler : ActionQualifierHandler(SET) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val rsName = "${actionInfo.name}_S_FF"
        data.run {
            moduleRS(rsName, stepsWithThisActionBlock(steps), actionInfo.resetExpr)
            oredAssign(SymbolicReference(actionInfo.actionQ), subRef(rsName, "Q1"))
        }
    }
}

object TimeLimited : ActionQualifierHandler(TIME_LIMITED) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val tonName = "${actionInfo.name}_L_TMR"
        val stepsL = stepsWithThisActionBlock(steps)
        data.run {
            moduleTON(tonName, stepsL, SymbolicReference(actionInfo.actionT))
            oredAndNotAssign(SymbolicReference(actionInfo.actionQ), stepsL, subRef(tonName, "Q"))
        }
    }
}

object TimeDelayed : ActionQualifierHandler(STORE_DELAYED) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val tonName = "${actionInfo.name}_D_TMR"
        data.run {
            moduleTON(tonName, stepsWithThisActionBlock(steps), SymbolicReference(actionInfo.actionT))
            oredAssign(SymbolicReference(actionInfo.actionQ), subRef(tonName, "Q"))
        }
    }
}

object Pulse : ActionQualifierHandler(PULSE) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val trigName = "${actionInfo.name}_P_TRIG"
        data.run {
            moduleTRIG(trigName, stepsWithThisActionBlock(steps))
            oredAssign(SymbolicReference(actionInfo.actionQ), subRef(trigName, "Q"))
        }
    }
}

object StoreAndDelay : ActionQualifierHandler(STORE_AND_DELAY) {
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

object DelayedAndStored : ActionQualifierHandler(DELAYED_AND_STORED) {
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

object StoreAndLimited : ActionQualifierHandler(STORE_AND_LIMITED) {
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

object Rising : ActionQualifierHandler(RAISING) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val trigName = "${actionInfo.name}_P1_TRIG"
        data.run {
            moduleTRIG(trigName, stepsWithThisActionBlock(steps))
            oredAssign(SymbolicReference(actionInfo.actionQ), subRef(trigName, "Q"))
        }
    }
}

object Falling : ActionQualifierHandler(FALLING) {
    override fun invoke(actionInfo: ActionInfo, steps: Set<String>, data: PipelineData) {
        val trigName = "${actionInfo.name}_P0_TRIG"
        data.run {
            moduleTRIG(trigName, stepsWithThisActionBlock(steps), "F_TRIG")
            oredAssign(SymbolicReference(actionInfo.actionQ), subRef(trigName, "Q"))
        }
    }
}

data class PipelineData(
    val network: SFCNetwork,
    val name: String,
    val index: Int,
    val scope: Scope,
    val finalScan: Boolean,
    val sfcFlags: Boolean,
    val maxNeededTokens: TokenAmount,
) {
    val tokenIsBoundedTo1: Boolean = maxNeededTokens is TokenAmount.Bounded && maxNeededTokens.max == 1
    val transitions: Map<MutableSet<SFCStep>, List<SFCTransition>> = network.steps.flatMap { it.outgoing }.distinct()
        .sortedByDescending { it.priority }.groupBy { it.from }
    val actions: MutableMap<String, ActionInfo> = mutableMapOf()

    val specialResetStatements: StatementList = StatementList()
    var stBody = StatementList()

    val structSfcStep: RecordType by lazy {
        val a = try {
            scope.resolveDataType0(STRUCT_SFC_STEP_NAME) as? RecordType
        } catch (e: DataTypeNotDefinedException) {
            null
        }
        a ?: RecordType(STRUCT_SFC_STEP_NAME)
        // throw IllegalArgumentException("Could not find $STRUCT_SFC_STEP_NAME in the given scope. See StepStructureTypes in the builtins")
    }

    val stateName = SymbolicReference(if (index <= 0) "_state" else "_${index}_state")
    val enumName =
        (if (index <= 0) "STATES_$name" else "STATES_$name\$$index").uppercase(Locale.getDefault())
    val stateEnumType =
        createEnumerationTypeForSfc(enumName, network, this::enumStepName)

    val stateEnumTypeDeclaration by lazy {
        val enumType = EnumerationTypeDeclaration(enumName)
        val et = stateEnumType
        enumType.addValue(CommonToken(IEC61131Lexer.IDENTIFIER, enumStepName(stepName(et.defValue))))
        et.allowedValues
            .map { it.key }
            .filter { it != et.defValue }
            .forEach {
                enumType.addValue(CommonToken(IEC61131Lexer.IDENTIFIER, enumStepName(stepName(it))))
            }
        // enumType.initialization = IdentifierInitializer(value = enumStepName(network.initialStep!!.name))
        // scope.dataTypes.register(enumName, enumType)
        // specialResetStatements += enumName.assignTo(enumType.initialization!!.value!!)
        enumType
    }

    init {
        network.steps.forEach { step ->
            step.events.forEach {
                val qualifier = it.qualifier ?: SFCActionQualifier(NON_STORED)
                val stepName = stepName(step.name)
                val actionName = it.actionName.replace('.', '_')
                if (actions.containsKey(actionName)) {
                    actions.getValue(actionName).addActionBlock(qualifier, stepName)
                } else {
                    actions[actionName] = ActionInfo(it.actionName, qualifier, stepName)
                }
            }
        }
    }

    fun enumValue(step: SFCStep) = EnumLit(stateEnumType, enumStepName(stepName(step.name)))

    fun stepName(stepName: String, idx: Int = index, sfcName: String = name): String = if (idx <=
        0
    ) {
        stepName
    } else {
        "_${idx}_$stepName"
    }

    // 0 -> "$sfcName$stepName"
    // else -> "$sfcName${idx}_$stepName"

    fun enumStepName(stepName: String) = if (index <= 0) stepName else "_${index}_$stepName"

    fun addToScope(name: String, dt: AnyDt, type: Int = 0): VariableDeclaration = if (!scope.variables.contains(name)) {
        VariableDeclaration(name, type, dt).also { scope.variables.add(it) }
    } else {
        scope.variables[name]!!
    }

    fun addToScope(names: List<String>, dt: AnyDt, type: Int = 0) = names.map { addToScope(it, dt, type) }

    fun moduleTON(name: String, input: Expression, pt: Expression) {
        specialResetStatements += InvocationStatement(
            SymbolicReference(name),
            mutableListOf(
                InvocationParameter(
                    "IN",
                    false,
                    LFALSE,
                ),
                InvocationParameter("PT", false, TimeLit(TimeData())),
            ),
        )
        moduleFB(name, "TON", listOf(Pair("IN", input), Pair("PT", pt)))
    }

    fun moduleRS(name: String, set: Expression, reset1: Expression) {
        specialResetStatements += InvocationStatement(
            SymbolicReference(name),
            mutableListOf(InvocationParameter("R", false, LTRUE)),
        )
        moduleFB(name, "RS", listOf(Pair("SET", set), Pair("RESET1", reset1)))
    }

    fun moduleTRIG(name: String, clk: Expression, type: String = "R_TRIG") {
        specialResetStatements += InvocationStatement(
            SymbolicReference(name),
            mutableListOf(InvocationParameter("CLK", false, LFALSE)),
        )
        moduleFB(name, type, listOf(Pair("CLK", clk)))
    }

    private fun moduleFB(name: String, type: String, parameters: List<Pair<String, Expression>>) {
        val vd = VariableDeclaration(name, SimpleTypeDeclaration(baseType = RefTo(type)))
        vd.type = VD_EXCLUDE_RESET
        scope.variables.add(vd)
        stBody.add(
            InvocationStatement(
                SymbolicReference(name),
                parameters.map { (left, right) ->
                    InvocationParameter(left, false, right)
                }.toMutableList(),
            ),
        )
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

    fun stateEnumValue(name: String): EnumLit = EnumLit(stateEnumType, name)
}

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
        if (actionStepsInQualifiers.contains(sfcActionQualifier.qualifier)) {
            actionStepsInQualifiers.getValue(sfcActionQualifier.qualifier).add(step)
        } else {
            actionStepsInQualifiers[sfcActionQualifier.qualifier] = mutableSetOf(step)
        }
    }
}

class TranslationSfcToStOld(
    network: SFCNetwork,
    val name: String,
    val index: Int = 0,
    val scope: Scope,
    sfcFlags: Boolean = true,
) : TranslationSfcToStPipeline(
    network,
    name,
    index,
    scope,
    false,
    sfcFlags,
    TokenAmount.Bounded(1),
) {

    private val transit = "__transit"

    init {
        pipelineSteps.clear()

        pipelineSteps += IntroduceStateEnumVariable
        pipelineSteps += IntroduceTransitVariable()
        pipelineSteps += TheBigStateCase(transit)
        if (sfcFlags) {
            pipelineSteps += SfcFlagIntroduction
        }
    }

    inner class IntroduceTransitVariable : PipelineStep {
        override fun invoke(data: PipelineData) {
            val vd = VariableDeclaration(transit, AnyBit.BOOL)
            vd.initValue = FALSE
            data.scope.variables += vd
        }
    }

    class TheBigStateCase(val transit: String) : PipelineStep {
        override fun invoke(data: PipelineData) {
            val theBigCase = CaseStatement()
            theBigCase.expression = data.stateName

            data.network.steps.forEach { step ->
                theBigCase.addCase(caseFor(data, step))
            }
            data.stBody.add(theBigCase)
        }

        fun caseFor(data: PipelineData, n: SFCStep): Case {
            val case = Case()
            val el = data.stateEnumValue(n.name)
            case.conditions.add(CaseCondition.Enumeration(el))
            val sl = case.statements
            // sl.comment("begin(State)")
            // sl.comment("begin(onEntry)")
            n.onEntry?.also {
                sl.add(
                    Statements.ifthen(
                        SymbolicReference(transit),
                        InvocationStatement(it),
                    ),
                )
            }
            sl.add(transit assignTo LFALSE)
            // sl.comment("end(onEntry)")

            // build in active
            // sl.comment("begin(onActive)")
            n.onWhile?.also {
                sl.add(InvocationStatement(it))
            }
            // sl.comment("end(onActive)")

            // sl.comment("begin(transition)")
            val transitions = IfStatement()
            val assignExitTrue = transit assignTo LTRUE

            n.outgoing.forEach {
                val assignNextState =
                    data.stateName assignTo data.stateEnumValue(it.to.first().name)
                transitions.addGuardedCommand(
                    it.guard,
                    assignExitTrue + assignNextState,
                )
            }
            sl.add(transitions)
            // sl.comment(("end(transition)"))

            // sl.comment("begin(onExit)")
            n.onExit?.also { onExit ->
                val ifExit = Statements.ifthen(
                    SymbolicReference(transit),
                    InvocationStatement(onExit),
                )
                sl.add(ifExit)
            }
            // sl.comment("end(onExit)")
            // sl.comment("end(State)")
            return case
        }
    }
}

private operator fun Statement.plus(statement: Statement): StatementList {
    val sl = StatementList()
    sl += this
    sl += statement
    return sl
}

internal fun createEnumerationTypeForSfc(enumName: String, network: SFCNetwork, enumStepName: (String) -> String) =
    EnumerateType(
        enumName,
        network.steps.map { enumStepName(it.name) }.toMutableList(),
        enumStepName(network.initialStep!!.name),
    )