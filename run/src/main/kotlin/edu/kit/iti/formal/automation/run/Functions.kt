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

class DefaultFunctionRegistry : FunctionRegistry {
    private val map = HashMap<String, FunctionEvaluator>()

    override fun register(name: String, func: FunctionEvaluator) {
        map[name] = func
    }

    override fun lookup(name: String): FunctionEvaluator? = map[name]
}

/*****************************************************************************/

object FunctionDefinitions {
    fun shiftLeftInt(num: EValue, bits: EValue): EValue {
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
    dfr.register(FunctionDefinitions::shiftLeftInt)
    return dfr
}

class AdapterFE(val kfunc: KFunction<EValue>) : FunctionEvaluator {
    override fun invoke(vararg args: EValue): EValue = kfunc.call(kfunc)
}