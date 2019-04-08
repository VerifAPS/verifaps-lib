package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.TimeType
import edu.kit.iti.formal.automation.datatypes.values.TimeData
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*

class TranslationToSt(private val index: Int = 0, private val network: SFCNetwork, val scope: Scope,
                      private val finalScan: Boolean = false) {
    val st = StatementList()
    var transitions: Map<MutableSet<SFCStep>, List<SFCTransition>> = mapOf()
    var actions: MutableMap<String, ActionInfo> = mutableMapOf()

    fun translate(): StatementList {
        this.assignStepVariables()
        this.processTransitions()
        this.controlActions()
        this.runActions()
        return this.st
    }

    fun getStatements(): StatementList {
        return this.st
    }

    fun assignStepVariables() {
        network.steps.forEach {
            val varName = stepName(it.name)
            if (!scope.variables.contains(varName)) {
                var stepType = when (it.isInitial) {
                    true -> StepType.Type.XINIT
                    false -> StepType.Type.XT
                }
                scope.variables.add(VariableDeclaration(varName,
                        scope.resolveDataType(StepType.toLowerCaseString(stepType))))
            }
        }
    }

    fun processTransitions() {
        transitions = network.steps.flatMap { it.outgoing }.distinct()
                .sortedByDescending { it.priority }.groupBy { it.from }
        transitions.forEach { transition ->
            val ifBranches = mutableListOf<GuardedStatement>()
            transition.value.forEach {
                //guard will be wrong if a step in the second or higher network is referenced
                var transitionIf = it.guard
                val ifAssignments = StatementList()
                it.from.forEach { step ->
                    transitionIf = subRef(stepName(step.name), "X") and transitionIf
                    ifAssignments.add(assignSubRefExpr(stepName(step.name), "_X", BooleanLit(false)))
                }
                it.to.forEach { step ->
                    ifAssignments.add(assignSubRefExpr(stepName(step.name), "_X", BooleanLit(true)))
                    ifAssignments.add(assignSubRefExpr(stepName(step.name), "_T", TimeLit(TimeData())))
                }
                ifBranches.add(GuardedStatement(transitionIf, ifAssignments))
            }
            st.add(IfStatement(ifBranches))
        }
        assignAndReset()
    }

    fun controlActions() {
        puzzleActions()
        createTimeVars()
        buildActionControl()
    }

    fun runActions() {
        actions.keys.forEach {
            val actionQ = it + "_Q"
            if (scope.hasVariable(it)) {
                st.add(assignRefExpr(it, SymbolicReference(actionQ)))
            } else {
                st.add(IfStatement(mutableListOf(GuardedStatement(SymbolicReference(actionQ),
                        StatementList(InvocationStatement(SymbolicReference(it), mutableListOf()))))))
            }
            st.add(assignRefExpr(actionQ, BooleanLit(false)))
        }
        network.steps.forEach {
            val varName = stepName(it.name)
            st.add(IfStatement(mutableListOf(GuardedStatement(subRef(varName, "X"),
                    StatementList(assignSubRefExpr(varName, "T", BinaryExpression(subRef(varName, "T"),
                            Operators.ADD, SymbolicReference("CYCLE_TIME"))))))))
        }
    }

    private fun buildActionControl() {
        actions.forEach {
            val actionQ = it.key + "_Q"
            val actionT = it.key + "_T"
            scope.variables.add(VariableDeclaration(actionQ, AnyBit.BOOL))
            val stepsInQualifiers = it.value.actionStepsInQualifiers
            val qN = SFCActionQualifier.Qualifier.NON_STORED
            val qR = SFCActionQualifier.Qualifier.OVERRIDING_RESET
            val qS = SFCActionQualifier.Qualifier.SET
            val qL = SFCActionQualifier.Qualifier.TIME_LIMITED
            val qD = SFCActionQualifier.Qualifier.STORE_DELAYED
            val qP = SFCActionQualifier.Qualifier.PULSE
            val qSD = SFCActionQualifier.Qualifier.STORE_AND_DELAY
            val qDS = SFCActionQualifier.Qualifier.DELAYED_AND_STORED
            val qSL = SFCActionQualifier.Qualifier.STORE_AND_LIMITED
            val qP1 = SFCActionQualifier.Qualifier.RAISING
            val qP0 = SFCActionQualifier.Qualifier.FALLING
            val resettingSteps: Expression =
                    (stepsInQualifiers[qR]?.mapRef()?:listOf(BooleanLit(false))).chainORs()
            if (stepsInQualifiers.contains(qN)) {
                st.add(assignRefExpr(actionQ, stepsWithThisActionBlock(stepsInQualifiers.getValue(qN))))
            }
            if (stepsInQualifiers.contains(qS)) {
                val rsName = it.key + "_S_FF"
                moduleRS(rsName, stepsWithThisActionBlock(stepsInQualifiers.getValue(qS)), resettingSteps)
                oredAssign(SymbolicReference(actionQ), subRef(rsName, "Q1"))
            }
            if (stepsInQualifiers.contains(qL)) {
                val tonName = it.key + "_L_TMR"
                val stepsL = stepsWithThisActionBlock(stepsInQualifiers.getValue(qL))
                moduleTON(tonName, stepsL, SymbolicReference(actionT))
                oredAndNotAssign(SymbolicReference(actionQ), stepsL, subRef(tonName, "Q"))
            }
            if (stepsInQualifiers.contains(qD)) {
                val tonName = it.key + "_D_TMR"
                moduleTON(tonName, stepsWithThisActionBlock(stepsInQualifiers.getValue(qD)), SymbolicReference(actionT))
                oredAssign(SymbolicReference(actionQ), subRef(tonName, "Q"))
            }
            if (stepsInQualifiers.contains(qP)) {
                val trigName = it.key + "_P_TRIG"
                moduleRTRIG(trigName, stepsWithThisActionBlock(stepsInQualifiers.getValue(qP)))
                oredAssign(SymbolicReference(actionQ), subRef(trigName, "Q"))
            }
            if (stepsInQualifiers.contains(qSD)) {
                val rsName = it.key + "_SD_FF"
                val tonName = it.key + "_SD_TMR"
                moduleRS(rsName, stepsWithThisActionBlock(stepsInQualifiers.getValue(qSD)), resettingSteps)
                moduleTON(tonName, subRef(rsName, "Q1"), SymbolicReference(actionT))
                oredAssign(SymbolicReference(actionQ), subRef(tonName, "Q"))
            }
            if (stepsInQualifiers.contains(qDS)) {
                val tonName = it.key + "_DS_TMR"
                val rsName = it.key + "_DS_FF"
                moduleTON(tonName, stepsWithThisActionBlock(stepsInQualifiers.getValue(qDS)),
                        SymbolicReference(actionT))
                moduleRS(rsName, subRef(tonName, "Q"), resettingSteps)
                oredAssign(SymbolicReference(actionQ), subRef(tonName, "Q"))
            }
            if (stepsInQualifiers.contains(qSL)) {
                val rsName = it.key + "_SL_FF"
                val tonName = it.key + "_SL_TMR"
                val rsQ = subRef(rsName, "Q1")
                moduleRS(rsName, stepsWithThisActionBlock(stepsInQualifiers.getValue(qSL)), resettingSteps)
                moduleTON(tonName, rsQ, SymbolicReference(actionT))
                oredAndNotAssign(SymbolicReference(actionQ), rsQ, subRef(tonName, "Q"))
            }
            if (finalScan) {
                if (stepsInQualifiers.contains(qR)) { andedNotAssign(SymbolicReference(actionQ), resettingSteps) }
                val trigName = it.key + "_Q_TRIG"
                moduleFTRIG(trigName, SymbolicReference(actionQ))
                oredAssign(SymbolicReference(actionQ), subRef(trigName, "Q"))
            }
            if (stepsInQualifiers.contains(qP1)) {
                val trigName = it.key + "_P1_TRIG"
                moduleRTRIG(trigName, stepsWithThisActionBlock(stepsInQualifiers.getValue(qP1)))
                oredAssign(SymbolicReference(actionQ), subRef(trigName, "Q"))
            }
            if (stepsInQualifiers.contains(qP0)) {
                val trigName = it.key + "_P0_TRIG"
                moduleFTRIG(trigName, stepsWithThisActionBlock(stepsInQualifiers.getValue(qP0)))
                oredAssign(SymbolicReference(actionQ), subRef(trigName, "Q"))
            }
            if (!finalScan && stepsInQualifiers.contains(qR)) {
                andedNotAssign(SymbolicReference(actionQ), resettingSteps)
            }
        }
    }

    private fun moduleFTRIG(name: String, clk: Expression) {
        moduleFB(name, "F_TRIG", listOf(Pair("CLK", clk)))
    }

    private fun moduleRTRIG(name: String, clk: Expression) {
        moduleFB(name, "R_TRIG", listOf(Pair("CLK", clk)))
    }

    private fun moduleTON(name: String, input: Expression, pt: Expression) {
        moduleFB(name, "TON", listOf(Pair("IN", input), Pair("PT", pt)))
    }

    private fun moduleRS(name: String, set: Expression, reset1: Expression) {
        moduleFB(name, "RS", listOf(Pair("SET", set), Pair("RESET1", reset1)))
    }

    private fun moduleFB(name: String, type: String, parameters: List<Pair<String, Expression>>) {
        scope.variables.add(VariableDeclaration(name, SimpleTypeDeclaration("ANONYM", RefTo(type),
                null)))
        st.add(InvocationStatement(SymbolicReference(name), parameters.map { (left, right) -> InvocationParameter(left,
                false, right) }.toMutableList()))
    }

    private fun oredAssign(left: SymbolicReference, right: Expression) {
        st.add(AssignmentStatement(left, left or right))
    }

    private fun oredAndNotAssign(left: SymbolicReference, center: Expression, right: Expression) {
        oredAssign(left, center and UnaryExpression(Operators.NOT, right))
    }

    private fun andedNotAssign(left: SymbolicReference, right: Expression) {
        st.add(AssignmentStatement(left, left and UnaryExpression(Operators.NOT, right)))
    }

    private fun stepsWithThisActionBlock(stepNames: MutableSet<String>): Expression {
        return stepNames.mapRef().chainORs()
    }

    private inline fun Set<String>.mapRef(): List<Expression> {
        return map {name -> subRef(name, "X")}
    }

    private inline fun List<Expression>.chainORs(): Expression {
        return reduce { acc, s -> acc or s }
    }

    private fun createTimeVars() {
        actions.forEach {
            if (it.value.actionBlockPairs.fold(false) { acc, pair ->
                        acc || pair.first.hasTime() }) {
                val actionT = it.key + "_T"
                if(!scope.variables.contains(actionT)) {
                    scope.variables.add(VariableDeclaration(actionT, TimeType.TIME_TYPE))
                }
                val ifBranches = mutableListOf<GuardedStatement>()
                it.value.actionBlockPairs.filter { maybeTimedActionBlockPair ->
                    maybeTimedActionBlockPair.first.hasTime() }.forEach { timedActionBlockPair ->
                    ifBranches.add(GuardedStatement(subRef(timedActionBlockPair.second, "X"),
                            StatementList(assignRefExpr(actionT, timedActionBlockPair.first.time))))
                }
                st.add(IfStatement(ifBranches))
            }
        }
    }

    private fun puzzleActions() {
        network.steps.forEach { step -> step.events.forEach {
            val qualifier = it.qualifier?: SFCActionQualifier(SFCActionQualifier.Qualifier.NON_STORED)
            val name = stepName(step.name)
            if (actions.containsKey(it.actionName)) {
                actions.getValue(it.actionName).addActionBlock(qualifier, name)
            } else {
                actions[it.actionName] = ActionInfo(qualifier, name)
            }
        } }
    }

    private fun assignAndReset() {
        network.steps.forEach {
            val varName = stepName(it.name)
            st.add(assignSubRefSubRef(varName, "X"))
            st.add(assignSubRefSubRef(varName, "T"))
            st.add(assignSubRefExpr(varName, "_X", BooleanLit(false)))
            st.add(assignSubRefExpr(varName, "_T", TimeLit(TimeData())))
        }
    }

    private fun subRef(name: String, sub: String): SymbolicReference {
        return SymbolicReference(name, SymbolicReference(sub))
    }

    private fun assignRefExpr(name: String, expr: Expression): AssignmentStatement {
        return AssignmentStatement(SymbolicReference(name), expr)
    }

    private fun assignSubRefExpr(name: String, sub: String, expr: Expression): AssignmentStatement {
        return AssignmentStatement(subRef(name, sub), expr)
    }

    private fun assignSubRefSubRef(name: String, sub: String): AssignmentStatement {
        return AssignmentStatement(subRef(name, sub), subRef(name, '_' + sub))
    }

    private fun stepName(name: String): String {
        return if (index > 0) { index.toString() + '_' + name } else { name }
    }
}

object StepType {
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
}

class ActionInfo(sfcActionQualifier: SFCActionQualifier, step: String) {
    var actionBlockPairs: MutableList<Pair<SFCActionQualifier, String>> = mutableListOf()
    var actionStepsInQualifiers: MutableMap<SFCActionQualifier.Qualifier, MutableSet<String>> = mutableMapOf()

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