package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.RecordType
import edu.kit.iti.formal.automation.datatypes.values.RecordValue
import edu.kit.iti.formal.automation.datatypes.values.VVOID
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.DefaultInitValue
import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.st.ast.PouElements
import edu.kit.iti.formal.automation.st.ast.PouExecutable
import edu.kit.iti.formal.automation.visitors.Utils

object ExecutionFacade {
    fun execute(pous: PouElements): State =
            createExecutionContext(pous).executeCycle()

    fun createExecutionContext(pous: PouElements): IECExecutorContext {
        val program = Utils.findProgram(pous)
        return when (program) {
            null -> throw IllegalArgumentException()
            else -> {
                return createExecutionContext(pous, program)
            }
        }
    }

    public fun createExecutionContext(pous: PouElements, program: PouExecutable): IECExecutorContext {
        if (program !in pous)
            pous.add(program)
        IEC61131Facade.resolveDataTypes(pous)
        return IECExecutorContext(pous, program)
    }

    fun createInitialState(pous: PouElements): State {
        return createExecutionContext(pous).initialState
    }

    fun createInitialState(entry: PouExecutable): State =
            createInitialState(entry.scope)

    fun createInitialState(scope: Scope): State {
        val v = DefaultInitValue.getInit(RecordType(scope.variables))
                as Value<RecordType, RecordValue>
        return State(v.value.fieldValues)
    }

    fun evaluateFunction(func: FunctionDeclaration, params: List<EValue>): EValue {
        val state = createInitialState(func.scope)
        setMatchingArgToParam(params, func.scope.variables, state)
        val runtime = Runtime(state, func.scope)
        runtime.visit(func.stBody!!)
        return if (func.returnType.obj != AnyDt.VOID)
            runtime.state[func.name]!!
        else VVOID
    }

    private fun setMatchingArgToParam(parameters: List<EValue>,
                                      vscope: VariableScope,
                                      state: State) {
        vscope.filter { it.isInput }
                .forEachIndexed { i, vd -> state[vd.name] = parameters[i] }
    }

    fun getDefaultValue(dataType: AnyDt): EValue = DefaultInitValue.getInit(dataType)
    fun evaluateExpression(state: State, scope: Scope, expression: Expression): EValue =
            expression.accept(ExpressionVisitor(state, scope))
}

class IECExecutorContext(val ast: PouElements, val entryPoint: PouExecutable) {
    val states: MutableList<State> = arrayListOf()
    val initialState: State
    val lastState: State
        get() = states[states.size - 1]

    init {
        states.add(ExecutionFacade.createInitialState(entryPoint))
        initialState = states[0]
    }

    fun executeCode(State: State): State {
        val runtime = Runtime(State)
        ast.accept(runtime)
        return State
    }

    fun executeCycle(vararg inputs: Pair<String, EValue>): State {
        val inputState = State()
        inputs.forEach { (t, v) -> inputState[t] = v }
        return executeCycle(input = inputState)
    }

    fun executeCycle(state: State = states[states.size - 1],
                     input: State = State()): State {
        val s = state.clone()
        s += input
        val rt = Runtime(s, entryPoint.scope)
        entryPoint.accept(rt)
        states += s
        return s
    }
}
