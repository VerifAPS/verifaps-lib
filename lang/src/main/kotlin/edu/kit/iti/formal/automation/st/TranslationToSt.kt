package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.TimeType
import edu.kit.iti.formal.automation.datatypes.values.TimeData
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.NON_STORED
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.OVERRIDING_RESET
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.SET
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.TIME_LIMITED
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.STORE_DELAYED
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.PULSE
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.STORE_AND_DELAY
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.DELAYED_AND_STORED
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.STORE_AND_LIMITED
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.RAISING
import edu.kit.iti.formal.automation.st.ast.SFCActionQualifier.Qualifier.FALLING
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor

class TranslationToSt(private val index: Int = 0, private val network: SFCNetwork, val scope: Scope,
                      private val finalScan: Boolean = false, private val sfcFlags: Boolean = false) {
    var st = StatementList()
    var transitions: Map<MutableSet<SFCStep>, List<SFCTransition>> = mapOf()
    var actions: MutableMap<String, ActionInfo> = mutableMapOf()

    init {
        transitions = network.steps.flatMap { it.outgoing }.distinct().sortedByDescending {
            it.priority }.groupBy { it.from }
        initActionDatastructure()
    }

    fun get(): StatementList { //TODO
        this.assignStepVariables()
        this.processTransitions()
        this.controlActions()
        this.runActions()
        this.addSfcFlags()
        return this.st
    }

    fun getStatements(): StatementList {
        return this.st
    }

    fun assignStepVariables() {
        IEC61131Facade.resolveDataTypes(BuiltinLoader.loadDefault(), scope)
        network.steps.forEach {
            val varName = stepName(it.name)
            if (!scope.variables.contains(varName)) {
                if (it.isInitial) {
                    scope.variables.add(VariableDeclaration(varName, scope.resolveDataType("xt"))) //TODO
                } else {
                    scope.variables.add(VariableDeclaration(varName, scope.resolveDataType("xt")))
                }
            }
        }
    }

    fun processTransitions() {
        transitions.forEach { transition ->
            val ifBranches = mutableListOf<GuardedStatement>()
            transition.value.forEach {
                var guard = ExpressionList(mutableListOf(it.guard))
                if (index > 0) {
                    AstMutableVisitorWithReplacedStepNames().visit(guard)
                }
                var transitionIf = guard.first()
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
            val resettingSteps: Expression =
                    (stepsInQualifiers[OVERRIDING_RESET]?.mapRef()?:listOf(BooleanLit(false))).chainORs()
            if (NON_STORED in stepsInQualifiers) {
                st.add(assignRefExpr(actionQ, stepsWithThisActionBlock(stepsInQualifiers.getValue(NON_STORED))))
            }
            if (SET in stepsInQualifiers) {
                val rsName = it.key + "_S_FF"
                moduleRS(rsName, stepsWithThisActionBlock(stepsInQualifiers.getValue(SET)), resettingSteps)
                oredAssign(SymbolicReference(actionQ), subRef(rsName, "Q1"))
            }
            if (TIME_LIMITED in stepsInQualifiers) {
                val tonName = it.key + "_L_TMR"
                val stepsL = stepsWithThisActionBlock(stepsInQualifiers.getValue(TIME_LIMITED))
                moduleTON(tonName, stepsL, SymbolicReference(actionT))
                oredAndNotAssign(SymbolicReference(actionQ), stepsL, subRef(tonName, "Q"))
            }
            if (STORE_DELAYED in stepsInQualifiers) {
                val tonName = it.key + "_D_TMR"
                moduleTON(tonName, stepsWithThisActionBlock(stepsInQualifiers.getValue(STORE_DELAYED)),
                        SymbolicReference(actionT))
                oredAssign(SymbolicReference(actionQ), subRef(tonName, "Q"))
            }
            if (PULSE in stepsInQualifiers) {
                val trigName = it.key + "_P_TRIG"
                moduleRTRIG(trigName, stepsWithThisActionBlock(stepsInQualifiers.getValue(PULSE)))
                oredAssign(SymbolicReference(actionQ), subRef(trigName, "Q"))
            }
            if (STORE_AND_DELAY in stepsInQualifiers) {
                val rsName = it.key + "_SD_FF"
                val tonName = it.key + "_SD_TMR"
                moduleRS(rsName, stepsWithThisActionBlock(stepsInQualifiers.getValue(STORE_AND_DELAY)), resettingSteps)
                moduleTON(tonName, subRef(rsName, "Q1"), SymbolicReference(actionT))
                oredAssign(SymbolicReference(actionQ), subRef(tonName, "Q"))
            }
            if (DELAYED_AND_STORED in stepsInQualifiers) {
                val tonName = it.key + "_DS_TMR"
                val rsName = it.key + "_DS_FF"
                moduleTON(tonName, stepsWithThisActionBlock(stepsInQualifiers.getValue(DELAYED_AND_STORED)),
                        SymbolicReference(actionT))
                moduleRS(rsName, subRef(tonName, "Q"), resettingSteps)
                oredAssign(SymbolicReference(actionQ), subRef(tonName, "Q"))
            }
            if (STORE_AND_LIMITED in stepsInQualifiers) {
                val rsName = it.key + "_SL_FF"
                val tonName = it.key + "_SL_TMR"
                val rsQ = subRef(rsName, "Q1")
                moduleRS(rsName, stepsWithThisActionBlock(stepsInQualifiers.getValue(STORE_AND_LIMITED)),
                        resettingSteps)
                moduleTON(tonName, rsQ, SymbolicReference(actionT))
                oredAndNotAssign(SymbolicReference(actionQ), rsQ, subRef(tonName, "Q"))
            }
            if (finalScan) {
                if (stepsInQualifiers.contains(OVERRIDING_RESET)) { andedNotAssign(SymbolicReference(actionQ),
                        resettingSteps) }
                val trigName = it.key + "_Q_TRIG"
                moduleFTRIG(trigName, SymbolicReference(actionQ))
                oredAssign(SymbolicReference(actionQ), subRef(trigName, "Q"))
            }
            if (RAISING in stepsInQualifiers) {
                val trigName = it.key + "_P1_TRIG"
                moduleRTRIG(trigName, stepsWithThisActionBlock(stepsInQualifiers.getValue(RAISING)))
                oredAssign(SymbolicReference(actionQ), subRef(trigName, "Q"))
            }
            if (FALLING in stepsInQualifiers) {
                val trigName = it.key + "_P0_TRIG"
                moduleFTRIG(trigName, stepsWithThisActionBlock(stepsInQualifiers.getValue(FALLING)))
                oredAssign(SymbolicReference(actionQ), subRef(trigName, "Q"))
            }
            if (!finalScan && stepsInQualifiers.contains(OVERRIDING_RESET)) {
                andedNotAssign(SymbolicReference(actionQ), resettingSteps)
            }
        }
    }

    fun addSfcFlags() {
        if (sfcFlags) {
            val newSt = StatementList()
            val ifAssignments = StatementList()
            scope.variables.forEach {
                //TODO
                ifAssignments.add(AssignmentStatement(SymbolicReference(it.name)))
            }
            addToScope(listOf("SFCInit", "SFCReset", "SFCPause"), AnyBit.BOOL)
            newSt.add(IfStatement(mutableListOf(GuardedStatement(SymbolicReference("SFCInit") or
                    SymbolicReference("SFCReset"), ifAssignments))))
            newSt.add(IfStatement(mutableListOf(GuardedStatement(UnaryExpression(Operators.NOT,
                    SymbolicReference("SFCInit") or SymbolicReference("SFCPause")), st))))
            st = newSt
        }
    }

    private fun addToScope(name: String, type: AnyDt) {
        if (!scope.variables.contains(name)) {
            scope.variables.add(VariableDeclaration(name, type))
        }
    }

    private fun addToScope(names: List<String>, type: AnyDt) {
        names.forEach { addToScope(it, type) }
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
                addToScope(actionT, TimeType.TIME_TYPE)
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

    private fun initActionDatastructure() {
        network.steps.forEach { step -> step.events.forEach {
            val qualifier = it.qualifier?: SFCActionQualifier(NON_STORED)
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

    private inner class AstMutableVisitorWithReplacedStepNames : AstMutableVisitor() {
        override fun visit(symbolicReference: SymbolicReference): Expression {
            for (i in 0 until network.steps.size - 1) {
                if (symbolicReference.identifier == network.steps[i].name) {
                    symbolicReference.identifier = stepName(network.steps[i].name)
                    break
                }
            }
            return super.visit(symbolicReference) as SymbolicReference
        }
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