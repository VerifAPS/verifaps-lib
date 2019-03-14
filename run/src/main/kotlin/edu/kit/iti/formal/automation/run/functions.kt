package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.values.VAnyInt
import kotlin.reflect.KFunction

/**
 *
 * @author Alexander Weigl
 * @version 1 (16.07.18)
 */
interface FunctionEvaluator {
    operator fun invoke(vararg args: EValue): EValue
}

interface FunctionRegistry {
    fun register(name: String, func: FunctionEvaluator)
    fun register(name: String, func: (Array<EValue>) -> EValue) {
        register(name, func as FunctionEvaluator)
    }

    fun lookup(name: String): FunctionEvaluator?

    operator fun set(name: String, func: FunctionEvaluator) = register(name, func)
    operator fun get(name: String) = lookup(name)

    operator fun invoke(name: String, args: Array<EValue>): EValue? = this[name]?.invoke(*args)

    fun register(kfunc: KFunction<EValue>) {
        register(kfunc.name, AdapterFE(kfunc))
    }
}

class DefaultFunctionRegistry() : FunctionRegistry {
    private val map = HashMap<String, FunctionEvaluator>()

    override fun register(name: String, func: FunctionEvaluator) {
        map[name] = func
    }

    override fun lookup(name: String): FunctionEvaluator? = map[name]
}

/*****************************************************************************/

object FunctionDefinitions {
    fun __shl_int(num: EValue, bits: EValue): EValue {
        if (num is VAnyInt && bits is VAnyInt) {
            val (dt, v) = num
            val (_, b) = bits
            return VAnyInt(dt, v.shiftLeft(b.toInt()))
        }
        throw IllegalArgumentException()
    }
}

fun getDefaultRegistry(): FunctionRegistry {
    val dfr = DefaultFunctionRegistry()
    dfr.register(FunctionDefinitions::__shl_int)
    return dfr
}

class AdapterFE(val kfunc: KFunction<EValue>) : FunctionEvaluator {
    override fun invoke(vararg args: EValue): EValue = kfunc.call(kfunc)
}
