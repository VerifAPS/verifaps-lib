package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.run.stexceptions.StEvaluationException
import edu.kit.iti.formal.automation.run.stexceptions.TypeMissmatchException
import edu.kit.iti.formal.automation.scope.GlobalScope
import edu.kit.iti.formal.automation.scope.LocalScope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.automation.visitors.Visitable
import mu.KLogging
import java.util.*

/**
 * Represents the Runtime of ST-execution
 * changes the [state] depending on the visited Nodes
 */
class Runtime(val state: State, private val definitionScopeStack: Stack<LocalScope> = Stack()) : DefaultVisitor<Unit>() {
    companion object : KLogging()
    /*
     * stores the variable definitions (e.g. "VAR a : INT END_VAR"
     * The variables are scoped, hence the Stack data-type
     */
    private val typeDeclarationAdder = TypeDeclarationAdder()

    override fun visit(variableDeclaration: VariableDeclaration) {
        variableDeclaration.init
        return super.visit(variableDeclaration)
    }
    override fun defaultVisit(visitable: Visitable?)  {
        TODO("method not implemented for: $visitable")
    }

    override fun visit(typeDeclarations: TypeDeclarations?) {
        typeDeclarations?.forEach { (it as Visitable).accept<Unit>(this) }
    }

    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
        typeDeclarationAdder.queueTypeDeclaration(enumerationTypeDeclaration)
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        typeDeclarationAdder.queueFunctionBlockDeclaration(functionBlockDeclaration)
    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        typeDeclarationAdder.queueFunctionDeclaration(functionDeclaration)
    }

    override fun visit(programDeclaration: ProgramDeclaration) {
        val localScope = programDeclaration.localScope
        definitionScopeStack.push(localScope)
        typeDeclarationAdder.addQueuedDeclarations(localScope.globalScope)
        initializeLocalVariables(localScope)

        return programDeclaration!!.programBody.accept(this)
    }

    override fun visit(fbc: FunctionBlockCallStatement) {
        val innerState = TopState()
        fbc.parameters.filter { !it.isOutput }.forEach {
            val parameterValue = (it.expression as Visitable).accept<ExpressionValue>(ExpressionVisitor(state, peekLocalScope()))
            innerState.put(it.name, Optional.of(parameterValue))
        }
        val fbName = fbc.functionBlockName
        val fbTypeName = peekLocalScope().getVariable(fbName).typeDeclaration.baseTypeName
        val fb = peekLocalScope().globalScope.getFunctionBlock(fbTypeName)
        fb.accept<Any>(Runtime(innerState))
        fbc.outputParameters.forEach {
            val parameterValue = (it.expression as Visitable).accept<ExpressionValue>(ExpressionVisitor(innerState, peekLocalScope()))
            state.put(it.name, Optional.of(parameterValue))
        }
    }

    override fun visit(whileStatement: WhileStatement) {
        fun checkCondition() = (whileStatement.condition as Visitable).accept(ExpressionVisitor(state, peekLocalScope()))
        while(checkCondition().value == true) {
            whileStatement.statements.accept(this)
        }
    }

    override fun visit(repeatStatement: RepeatStatement) {
        fun checkCondition() = (repeatStatement.condition as Visitable).accept(ExpressionVisitor(state, peekLocalScope()))
        do {
            repeatStatement.statements.accept(this)
        } while (checkCondition().value == false)
    }

    override fun visit(forStatement: ForStatement) {
        val variableName = forStatement.variable
        val startValue = (forStatement.start as Visitable).accept<ExpressionValue>(ExpressionVisitor(state, peekLocalScope()))
        val stopValue = (forStatement.stop as Visitable).accept<ExpressionValue>(ExpressionVisitor(state, peekLocalScope()))
        val stepValue = (forStatement.step as Visitable).accept<ExpressionValue>(ExpressionVisitor(state, peekLocalScope()))
        state.put(variableName, Optional.of(startValue))

        fun conditionHolds() : Boolean {
            val variableValue = state[variableName] ?: return false
            logger.debug { "Does the ForStatement-Condition hold? current: $variableValue stopValue: $stopValue" }
            return variableValue.map {
                OperationEvaluator.lessThan(it, stopValue)
            }.orElseThrow {
                StEvaluationException("variable $variableName not found")
            }.value
        }

        while(conditionHolds()) {
            logger.debug { "for-loop-condition still holds. execute statement body" }
            forStatement.statements.accept(this)

            val variableValue = state[variableName]
            logger.debug { "increase for-loop variable ($variableValue) by step ($stepValue)" }
            state[variableName] = variableValue!!.map { OperationEvaluator.add(it, stepValue) }
        }
    }

    public fun initializeLocalVariables(localScope: LocalScope) {
        val localVariables: Map<out String, VariableDeclaration> = localScope.localVariables
        localVariables.map {
            val initExpr = it.value.init
            val initialValue : Optional<ExpressionValue> = when(initExpr) {
                null -> Optional.empty()
                else -> Optional.of(initExpr.accept<ExpressionValue>(
                        ExpressionVisitor(state, peekLocalScope())
                ) as ExpressionValue)
            }

            state.put(it.key, initialValue)
        }
    }

    private fun chooseGuardedStatement(ifStatement: IfStatement) : GuardedStatement? {
        for (statement in ifStatement.conditionalBranches) {
            val returnValue: ExpressionValue = (statement.condition as Visitable)
                    .accept<ExpressionValue>(
                            ExpressionVisitor(state, peekLocalScope())
                    )
            if (returnValue.value is Boolean) {
                if (returnValue.value == true) {
                    return statement
                }
                //if returnValue is false -> continue to search with the next guarded statement
            } else {
                throw TypeMissmatchException("condition for if statement must be a boolean")
            }
        }
        return null
    }

    override fun visit(ifStatement: IfStatement) {
        val chosenGuardedStatement = chooseGuardedStatement(ifStatement)
        if (chosenGuardedStatement != null) {
            chosenGuardedStatement.accept<Any>(this) // will run visit(GuardedStatement)
            return
        }
        val elseBranch = ifStatement.elseBranch
        elseBranch.accept(this)
    }

    override fun visit(guardedStatement: GuardedStatement) {
        guardedStatement.statements.accept(this)
    }

    override fun visit(statements: StatementList?) {
        statements!!.forEach {
            logger.debug { "Executing statement $it" }
            it.accept<Any>(this)
        }
    }

    override fun visit(assignmentStatement: AssignmentStatement) {
        val expressionVisitor = ExpressionVisitor(state, peekLocalScope())
        val expressionValue = assignmentStatement.expression.accept<ExpressionValue>(expressionVisitor) as ExpressionValue
        val nodeName = assignmentStatement.location.accept<Any>(object : DefaultVisitor<Unit>() {
            override fun visit(symbolicReference: SymbolicReference) {
                state.updateValue(symbolicReference.identifier, expressionValue)
                logger.debug { """ "${symbolicReference.identifier}" now as value $expressionValue""" }
            }

            override fun visit(deref: Deref) {
                TODO("implement")
            }
        })

    }

    private fun peekLocalScope() = definitionScopeStack.peek()
}