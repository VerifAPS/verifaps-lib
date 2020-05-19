package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType
import edu.kit.iti.formal.automation.datatypes.RecordType
import edu.kit.iti.formal.automation.datatypes.UINT
import edu.kit.iti.formal.automation.datatypes.values.RecordValue
import edu.kit.iti.formal.automation.datatypes.values.VAnyInt
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.run.stexceptions.TypeMissmatchException
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitorNN
import edu.kit.iti.formal.automation.visitors.Visitable
import edu.kit.iti.formal.util.debug
import java.math.BigInteger
import java.util.*

/**
 * Represents the Runtime of ST-execution
 * changes the [state] depending on the visited Nodes
 */
class Runtime(val state: State, private val definitionScopeStack: Stack<Scope> = Stack())
    : DefaultVisitorNN<Unit>() {
    constructor(state: State, scope: Scope) : this(state) {
        definitionScopeStack.push(scope)
    }

    override fun defaultVisit(obj: Any) {
        TODO("method not implemented for: $obj")
    }

    override fun visit(programDeclaration: ProgramDeclaration) {
        val localScope = programDeclaration.scope
        definitionScopeStack.push(localScope)
        programDeclaration.stBody?.accept(this)
        definitionScopeStack.pop()
    }

    override fun visit(fbc: InvocationStatement) {
        val fbName = fbc.callee.identifier
        val innerValue = state[fbName]!! as Value<RecordType, RecordValue>
        val innerState = State(innerValue.value.fieldValues)
        val fbDataType =
                (peekScope().resolveVariable(fbc.callee)?.dataType) as FunctionBlockDataType?
                        ?: throw IllegalStateException()
        val fb = fbDataType.functionBlock

        fbc.parameters
                .filter { it.isInput }
                .forEach {
                    val parameterValue = evaluateExpression(it)
                    innerState[it.name!!] = parameterValue
                }

        val innerScope = Stack<Scope>()
        innerScope.push(fb.scope)
        fb.stBody?.accept(Runtime(innerState, innerScope))

        fbc.parameters
                .filter { it.isOutput }
                .forEach {
                    state[it.name!!] =
                            ExecutionFacade.evaluateExpression(innerState, fb.scope, it.expression)
                }


    }

    private fun evaluateExpression(it: InvocationParameter) =
            evaluateExpression(it.expression)

    private fun evaluateExpression(it: Expression) =
            it.accept(ExpressionVisitor(state, peekScope()))


    fun createCondition(expr: Expression): () -> Boolean =
            { expr.accept(ExpressionVisitor(state, peekScope())).value as Boolean }


    override fun visit(whileStatement: WhileStatement) {
        val condition = createCondition(whileStatement.condition)
        while (condition()) {
            whileStatement.statements.accept(this)
        }
    }

    override fun visit(repeatStatement: RepeatStatement) {
        val condition = createCondition(repeatStatement.condition)
        do {
            repeatStatement.statements.accept(this)
        } while (!condition())
    }

    override fun visit(forStatement: ForStatement) {
        val variableName = forStatement.variable
        val startValue = forStatement.start.accept(ExpressionVisitor(state, peekScope()))
        val stopValue = forStatement.stop.accept(ExpressionVisitor(state, peekScope()))
        val stepValue = forStatement.step?.accept(ExpressionVisitor(state, peekScope()))
                ?: VAnyInt(UINT, BigInteger.ONE)

        state[variableName] = startValue

        fun conditionHolds(): Boolean {
            val variableValue = state[variableName] ?: return false
            debug("Does the ForStatement-Condition hold? current: $variableValue stopValue: $stopValue")
            return OperationEvaluator.lessThan(variableValue, stopValue).value
        }

        while (conditionHolds()) {
            debug("for-loop-condition still holds. execute statement body")
            forStatement.statements.accept(this)

            val variableValue = state[variableName]
            debug("increase for-loop variable ($variableValue) by step ($stepValue)")
            state[variableName] = OperationEvaluator.add(state[variableName]!!, stepValue)
        }
    }

    /*
    public fun defaultValueForDataType(dataType: VariableDeclaration): Optional<EValue> {
        //(it.value.dataType as FunctionBlockDataType).functionBlock.localScope
        if (dataType == null) {
            TODO()
        }
        return when (dataType.dataType) {
            isType FunctionBlockDataType -> {
                val innerState = TopState()
                val innerStack = Stack<Scope>()
                innerStack.push((dataType.dataType as FunctionBlockDataType).functionBlock.scope)
                val innerRuntime = Runtime(innerState, innerStack)
                innerRuntime.initializeLocalVariables((dataType.dataType as FunctionBlockDataType).functionBlock.scope);

                val structValue = mutableMapOf<String, EValue>()
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
*/

    /*
    public fun initializeLocalVariables(localScope: Scope) {
        val localVariables: Map<out String, VariableDeclaration> = localScope.variables
        localVariables.map {
            val stateVal = state[it.key]
            if (stateVal != null && stateVal.isPresent) {
                return@map
            }
            val initExpr = it.value.init
            val initialValue : Optional<EValue> = when(initExpr) {
                null -> defaultValueForDataType(it.value);
                else -> Optional.of(initExpr.accept<EValue>(
                        ExpressionVisitor(state, peekScope())
                ) as EValue)
            }

            state.put(it.key, initialValue)
        }
    }*/

    private fun chooseGuardedStatement(ifStatement: IfStatement): GuardedStatement? {
        for (statement in ifStatement.conditionalBranches) {
            val returnValue: EValue = (statement.condition as Visitable)
                    .accept<EValue>(
                            ExpressionVisitor(state, peekScope())
                    )
            if (returnValue.value is Boolean) {
                if (returnValue.value == true) {
                    return statement
                }
                //if returnValue isType false -> continue to search with the next guarded statement
            } else {
                throw TypeMissmatchException("condition for if statement must be a boolean")
            }
        }
        return null
    }

    override fun visit(ifStatement: IfStatement) {
        val chosenGuardedStatement = chooseGuardedStatement(ifStatement)
        if (chosenGuardedStatement != null) {
            chosenGuardedStatement.accept(this) // will run visit(GuardedStatement)
            return
        }
        val elseBranch = ifStatement.elseBranch
        elseBranch.accept(this)
    }

    override fun visit(guardedStatement: GuardedStatement) {
        guardedStatement.statements.accept(this)
    }

    override fun visit(statements: StatementList) {
        statements.forEach {
            debug("Executing statement $it")
            it.accept(this)
        }
    }

    override fun visit(assignmentStatement: AssignmentStatement) {
        val expressionVisitor = ExpressionVisitor(state, peekScope())
        val expressionValue = assignmentStatement.expression.accept(expressionVisitor)
        val location = (assignmentStatement.location as SymbolicReference)
        val path = location.asPath()
        //var current = state[identifier]
        state[path] = expressionValue
    }

    private fun peekScope() = definitionScopeStack.peek()
}

fun SymbolicReference.asPath(): List<String> {
    val l = arrayListOf<String>()
    var cur = this
    do {
        l += cur.identifier
        cur = cur.sub ?: return l
    } while (true)
}
