package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType
import edu.kit.iti.formal.automation.datatypes.RecordType
import edu.kit.iti.formal.automation.run.stexceptions.ExecutionException
import edu.kit.iti.formal.automation.run.stexceptions.StEvaluationException
import edu.kit.iti.formal.automation.run.stexceptions.TypeMissmatchException
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.automation.visitors.Visitable
import mu.KLogging
import java.util.*

/**
 * Represents the Runtime of ST-execution
 * changes the [state] depending on the visited Nodes
 */
class Runtime (val state: State, private val definitionScopeStack: Stack<Scope> = Stack()) : DefaultVisitor<Unit>() {
    companion object : KLogging()
    /*
     * stores the variable definitions (e.g. "VAR a : INT END_VAR"
     * The variables are scoped, hence the Stack data-type
     */
    private val typeDeclarationAdder = TypeDeclarationAdder()

    override fun defaultVisit(visitable: Visitable?)  {
        TODO("method not implemented for: $visitable")
    }

    override fun visit(typeDeclarations: TypeDeclarations?) {
        typeDeclarations?.forEach { (it as Visitable).accept<Unit>(this) }
    }

    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
        typeDeclarationAdder.queueTypeDeclaration(enumerationTypeDeclaration)
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration) {
        typeDeclarationAdder.queueTypeStructureDeclaration(structureTypeDeclaration)
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {

        typeDeclarationAdder.queueFunctionBlockDeclaration(functionBlockDeclaration)
    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        typeDeclarationAdder.queueFunctionDeclaration(functionDeclaration)
    }

    override fun visit(programDeclaration: ProgramDeclaration) {
        val localScope = programDeclaration.scope
        definitionScopeStack.push(localScope)
        typeDeclarationAdder.addQueuedDeclarations(localScope)
        initializeLocalVariables(localScope)
        return programDeclaration!!.stBody.accept(this)
    }

    override fun visit(fbc: InvocationStatement) {
        val innerState = TopState()
        val fbName = fbc.calleeName
        val fbTypeName = peekScope().getVariable(fbName).typeDeclaration.baseTypeName
        val fbDataType = peekScope().resolveDataType(fbTypeName);
        val fb = peekScope().getFunctionBlock(fbTypeName)

        val fbPrevValue = state[fbName]!!.orElseThrow { ExecutionException("not initialized") }.value
        if (fbPrevValue is HashMap<*, *>) {
            fbPrevValue.forEach {
                innerState.put(it.key as String, Optional.of(it.value as ExpressionValue))
            }
        }


        fbc.parameters./*filter { !it.isOutput }.*/forEach {
            val parameterValue = (it.expression as Visitable).accept<ExpressionValue>(ExpressionVisitor(state, peekScope()))
            innerState.put(it.name, Optional.of(parameterValue))
        }


        val innerScope = Stack<Scope>()
        innerScope.push(peekScope().getFunctionBlock(fbTypeName).scope);

        fb.stBody.accept(Runtime(innerState, innerScope))

        val structValue = mutableMapOf<String, ExpressionValue>()
        innerState.forEach {
            val key = it.key
            it.value.ifPresent {
                structValue.put(key, it)
            }
        }
        if (fbDataType is RecordType) {

            state.put(fbName, Optional.of(StructValue(fbDataType, structValue)))
        } else {
            TODO()
        }

    }

    override fun visit(whileStatement: WhileStatement) {
        fun checkCondition() = (whileStatement.condition as Visitable).accept(ExpressionVisitor(state, peekScope()))
        while(checkCondition().value == true) {
            whileStatement.statements.accept(this)
        }
    }

    override fun visit(repeatStatement: RepeatStatement) {
        fun checkCondition() = (repeatStatement.condition as Visitable).accept(ExpressionVisitor(state, peekScope()))
        do {
            repeatStatement.statements.accept(this)
        } while (checkCondition().value == false)
    }

    override fun visit(forStatement: ForStatement) {
        val variableName = forStatement.variable
        val startValue = (forStatement.start as Visitable).accept<ExpressionValue>(ExpressionVisitor(state, peekScope()))
        val stopValue = (forStatement.stop as Visitable).accept<ExpressionValue>(ExpressionVisitor(state, peekScope()))
        val stepValue = (forStatement.step as Visitable).accept<ExpressionValue>(ExpressionVisitor(state, peekScope()))
        state.put(variableName, Optional.of(startValue))

        fun conditionHolds(): Boolean {
            val variableValue = state[variableName] ?: return false
            logger.debug { "Does the ForStatement-Condition hold? current: $variableValue stopValue: $stopValue" }
            return variableValue.map {
                OperationEvaluator.lessThan(it, stopValue)
            }.orElseThrow {
                StEvaluationException("variable $variableName not found")
            }.value
        }

        while (conditionHolds()) {
            logger.debug { "for-loop-condition still holds. execute statement body" }
            forStatement.statements.accept(this)

            val variableValue = state[variableName]
            logger.debug { "increase for-loop variable ($variableValue) by step ($stepValue)" }
            state[variableName] = variableValue!!.map { OperationEvaluator.add(it, stepValue) }
        }
    }

    public fun defaultValueForDataType(dataType: VariableDeclaration) : Optional<ExpressionValue> {
        //(it.value.dataType as FunctionBlockDataType).functionBlock.localScope
        if (dataType == null) {
            TODO()
        }
        return when(dataType.dataType) {
            is FunctionBlockDataType -> {
                val innerState = TopState()
                val innerStack = Stack<Scope>()
                innerStack.push((dataType.dataType as FunctionBlockDataType).functionBlock.scope)
                val innerRuntime = Runtime(innerState, innerStack)
                innerRuntime.initializeLocalVariables((dataType.dataType as FunctionBlockDataType).functionBlock.scope);

                val structValue = mutableMapOf<String, ExpressionValue>()
                innerState.forEach {
                    val key = it.key
                    it.value.ifPresent {
                        structValue.put(key, it)
                    }
                }
                return Optional.of(StructValue(dataType.dataType as FunctionBlockDataType, structValue))
            }
            else -> Optional.empty();
        }
    }


    public fun initializeLocalVariables(localScope: Scope) {
        val localVariables: Map<out String, VariableDeclaration> = localScope.variables
        localVariables.map {
            val stateVal = state[it.key]
            if (stateVal != null && stateVal.isPresent) {
                return@map
            }
            val initExpr = it.value.init
            val initialValue : Optional<ExpressionValue> = when(initExpr) {
                null -> defaultValueForDataType(it.value);
                else -> Optional.of(initExpr.accept<ExpressionValue>(
                        ExpressionVisitor(state, peekScope())
                ) as ExpressionValue)
            }

            state.put(it.key, initialValue)
        }
    }

    private fun chooseGuardedStatement(ifStatement: IfStatement) : GuardedStatement? {
        for (statement in ifStatement.conditionalBranches) {
            val returnValue: ExpressionValue = (statement.condition as Visitable)
                    .accept<ExpressionValue>(
                            ExpressionVisitor(state, peekScope())
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
            chosenGuardedStatement.accept<AnyDt>(this) // will run visit(GuardedStatement)
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
            it.accept<AnyDt>(this)
        }
    }

    override fun visit(assignmentStatement: AssignmentStatement) {
        val expressionVisitor = ExpressionVisitor(state, peekScope())
        val expressionValue = assignmentStatement.expression.accept<ExpressionValue>(expressionVisitor) as ExpressionValue
        val sub = (assignmentStatement.location as SymbolicReference).sub
        val identifier = (assignmentStatement.location as SymbolicReference).identifier
        var current = state[identifier]
        if (sub != null) {
            val subIdentifier = sub.accept<AnyDt>(object : DefaultVisitor<String>() {
                override fun visit(symbolicReference: SymbolicReference):String {
                    return symbolicReference.identifier
                }

                override fun visit(deref: Deref): String {
                    TODO("implement")
                }
            })
            current!!.ifPresent({
                if (it is StructValue) {
                    val structValue = it.value
                    state.updateValue(identifier, StructValue(it.dataType, it.value.mapValues {
                        if (it.key == subIdentifier){
                            expressionValue
                        } else {
                            it.value
                        }}))
                }
            })
        } else {
            state.updateValue(identifier, expressionValue)
        }


    }

    private fun peekScope() = definitionScopeStack.peek()
}