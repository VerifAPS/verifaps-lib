package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.run.stexceptions.ExecutionException
import java.util.*


/**
 * State contains the variables values (-> the state of execution)
 * it contains value in the form of Optional<ExpressionValue>>. This form is needed since variables can be
 * initialized without a value. A variable that has not been defined will be "null" if queried
 * and will be Optional.empty() if defined but not initialized
 */
sealed class State : HashMap<String, Optional<ExpressionValue>>() {
    /**
     * returns the value of a variable, that has been initialized (e.g. has a value)
     * if the given variable has not been initialized the returned value will be null
     */
    fun getInitialized(key: String) : ExpressionValue? = get(key)?.orElse(null)

    fun defineVariable(key: String) = put(key, Optional.empty())

    fun updateValue(key: String, value: ExpressionValue): Optional<ExpressionValue>? {
        if (!isDefined(key)) throw ExecutionException("Variable \"$key\" is not defined")
        return put(key, Optional.of(value))
    }

    fun isInitialized(key: String) = get(key)?.isPresent ?: false // return true, if get(key) contains a value; false otherwise

    fun isDefined(key: String) = containsKey(key)
}


class TopState() : State()

class NestedState(val parentState: State) : State() {
    override fun get(key: String): Optional<ExpressionValue>? {
        return super.get(key) ?: return parentState[key]
    }

    override fun put(key: String, value: Optional<ExpressionValue>): Optional<ExpressionValue>? {
        if (parentState.contains(key)) {
            return parentState.put(key, value)
        }
        return super.put(key, value)
    }

    override fun containsKey(key: String): Boolean {
        return super.containsKey(key).or(parentState.containsKey(key))
    }

    override fun containsValue(value: Optional<ExpressionValue>): Boolean {
        return super.containsValue(value).or(parentState.containsValue(value))
    }

    override fun remove(key: String, value: Optional<ExpressionValue>): Boolean {
        val isRemoved = super.remove(key, value)
        if (isRemoved) return true
        return parentState.remove(key, value)
    }
}

