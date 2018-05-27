package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType
import edu.kit.iti.formal.automation.datatypes.RecordType
import edu.kit.iti.formal.automation.datatypes.TimeType
import edu.kit.iti.formal.automation.datatypes.values.RecordValue
import edu.kit.iti.formal.automation.datatypes.values.RuntimeVariable
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.datatypes.values.Values
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.run.stexceptions.ExecutionException
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.automation.visitors.Visitable
import jdk.nashorn.internal.ir.FunctionCall
import org.stringtemplate.v4.misc.STRuntimeMessage
import java.util.*

/**
 * evaluates the expression given via .visit() and runs creates a Runtime to call on functions in the expression.
 * ExpressionVisitor resolves variable values in [state] and declarations in [localScope]
 * ExpressionVisitor may modifies [state] indirectly through Runtime
 */
class ExpressionVisitor(private val state : State,
                        private val localScope : Scope) : DefaultVisitor<ExpressionValue>() {

    override fun defaultVisit(visitable: Visitable?): ExpressionValue {
        TODO("missing visitor for visitable ${visitable.toString()}")
    }

    override fun visit(structureInitialization: StructureInitialization): ExpressionValue {
        val structInitValues = structureInitialization.initValues.mapValues {
            (it.value as Visitable).accept<ExpressionValue>(ExpressionVisitor(state, localScope))
        }//.mapValues { RuntimeVariable(it.key) }
        return StructValue(RecordType(), structInitValues)
    }

    private fun setMatchingArgToParam(parameters: List<ExpressionValue>, arguments: Map<String, VariableDeclaration>, state: State) {
        val sortedArguments = arguments.entries
                .sortedBy {
                    print(it)
                    it.value.typeDeclaration.startPosition.offset
                }
                .map {
                    it.key
                }
        println(state)
        sortedArguments.forEachIndexed { i, name -> state.put(name, Optional.of(parameters[i])) }
        println(state)
    }


    override fun visit(functionCall: Invocation): ExpressionValue {
        val innerState = TopState()
        val functionDeclaration = localScope.getFunction(functionCall.calleeName)
        val definitionScopeStack = Stack<Scope>()
        //functionDeclaration.setScope(localScope)

        definitionScopeStack.push(functionDeclaration.scope)


        val runtime = Runtime(innerState, definitionScopeStack)

        runtime.initializeLocalVariables(functionDeclaration.scope)

        val evaluatedParams = functionCall.parameters.map { (it as Visitable).accept<ExpressionValue>(this) }
        setMatchingArgToParam(evaluatedParams, functionDeclaration.scope.variables, innerState)

        innerState[functionCall.calleeName] = Optional.empty();

        functionDeclaration.stBody.accept(runtime)
        val returnValue = innerState[functionCall.calleeName]

        if (returnValue != null) {
            return returnValue.orElseThrow { ExecutionException("Return value not set in function '${functionCall.calleeName}' declaration") }
        }
        throw ExecutionException("Return value not initialized in function ${functionCall.calleeName}")
    }

    override fun visit(unaryExpression: UnaryExpression): ExpressionValue {
        //"as ExpressionValue" should not be necessary, but the compiler complains otherwise
        // I see no way, where the result of .accept() will not be a ExpressionValue
        val expressionValue = unaryExpression.expression.accept<ExpressionValue>(this) as ExpressionValue
        return when(unaryExpression.operator) {
            Operators.NOT -> OperationEvaluator.not(expressionValue)
            Operators.MINUS -> OperationEvaluator.negate(expressionValue)
            else -> throw IllegalStateException("no other unary Operator")
        }
    }

    override fun visit(literal: Literal) : ExpressionValue {
        /*literal.asValue() does either throw an exception or returns null, if no direct value is available
        DISCUSS: is this intentional or accidental? better way distinguishing between RefTo and other?
        (is RefTo) did not work  -> solve be using resolveDataType*/
        try {
            val asValue = literal.asValue()
            if (asValue != null) {
                return asValue
            }
        } catch (npe : NullPointerException) {

        }

        val identifier = literal.dataTypeName
        val resolvedDataType = localScope.resolveDataType(identifier)
        if (resolvedDataType is EnumerateType) {
            return Values.VAnyEnum(resolvedDataType, literal.textValue)
        }
        //DISCUSS: Time-Literal has resolvedDataType LREAL ?!
        if (resolvedDataType is TimeType) {
            TODO()
            //return Values.VAnyReal(resolvedDataType, BigDecimal.valueOf(0))
        }
        TODO("implement other cases for $literal")
    }


    override fun visit(symbolicReference: SymbolicReference): ExpressionValue {
        val variableName = symbolicReference.identifier

        val variableState = state[variableName]
                ?: throw ExecutionException("Variable $variableName not found")

        var dataType = symbolicReference.dataType(localScope)
        if (dataType is FunctionBlockDataType) {
            val structValue = state[symbolicReference.identifier]!!.orElseThrow { ExecutionException("variable not defined") }.value
            if (symbolicReference.sub != null && structValue is Map<*, *>) {
                val matching = structValue.filter {
                    it.key == (symbolicReference.sub as SymbolicReference).identifier }.values.first()
                if (matching != null && matching is ExpressionValue) {
                    return matching
                }
            }
            TODO();
        }

        return variableState
                .orElseThrow { throw ExecutionException("Variable $variableName not initialized") }
    }

    override fun visit(binaryExpression: BinaryExpression): ExpressionValue {
        val leftValue = binaryExpression.leftExpr.accept<ExpressionValue>(this) as ExpressionValue
        val rightValue = binaryExpression.rightExpr.accept<ExpressionValue>(this) as ExpressionValue

        //TODO resolve function by using dataType
        //binaryExpression.dataType(localScope)

        return when(binaryExpression.operator) {
            Operators.ADD -> OperationEvaluator.add(leftValue, rightValue)
            Operators.MULT -> OperationEvaluator.multiply(leftValue, rightValue)
            Operators.EQUALS -> OperationEvaluator.equalValues(leftValue, rightValue)
            Operators.NOT_EQUALS -> OperationEvaluator.notEquals(leftValue, rightValue)
            Operators.GREATER_THAN -> OperationEvaluator.greaterThan(leftValue, rightValue)
            Operators.GREATER_EQUALS -> OperationEvaluator.greaterThanOrEquals(leftValue, rightValue)
            Operators.LESS_THAN -> OperationEvaluator.lessThan(leftValue, rightValue)
            Operators.LESS_EQUALS -> OperationEvaluator.lessThanOrEquals(leftValue, rightValue)
            Operators.AND -> OperationEvaluator.and(leftValue, rightValue)
            Operators.OR -> OperationEvaluator.or(leftValue, rightValue)
            Operators.SUB -> OperationEvaluator.subtract(leftValue, rightValue)
            Operators.MOD -> OperationEvaluator.modulo(leftValue, rightValue)
            else -> TODO("operator ${binaryExpression.operator.symbol()} is not implemented (${binaryExpression.operator.toString()})")
        }
    }


}

