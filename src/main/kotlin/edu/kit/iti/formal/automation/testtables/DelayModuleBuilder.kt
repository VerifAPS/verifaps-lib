/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables

import edu.kit.iti.formal.smv.ast.*
import java.lang.String

/**
 * created on 15.12.16
 *
 * @author Alexander Weigl
 * @version 1
 */
class DelayModuleBuilder(private val variable: SVariable, cycles: Int) : Runnable {
    val historyLength: Int
    private val datatype: SMVType?
    private var moduleType: SMVType? = null
    private var module = SMVModule()

    init {

        historyLength = Math.abs(cycles)
        assert(historyLength > 0)
        datatype = variable.datatype
        module.name = String.format("History_%d_of_%s", historyLength, variable.name)

        if (datatype == null)
            throw IllegalArgumentException("No datatype given")

    }

    override fun run() {
        // one module parameter
        val mp = SVariable("val", datatype)
        module.moduleParameter.add(mp)

        // state variables
        val vars = arrayOfNulls<SVariable>(historyLength + 1)
        vars[0] = mp
        for (i in 1..historyLength) {
            val v = SVariable("_$$i", datatype)
            vars[i] = v
            module.stateVars.add(v)
        }

        // next($<i>) = $<i-1>
        for (i in 1..vars.size) {
            module.nextAssignments.add(
                    SAssignment(vars[i], vars[i - 1])
            )
        }

        // type
        moduleType = SMVType.Module(module.name, variable)
    }

    fun getModuleType(): SMVType? {
        return moduleType
    }

    fun setModuleType(moduleType: SMVType): DelayModuleBuilder {
        this.moduleType = moduleType
        return this
    }

    fun getModule(): SMVModule {
        return module
    }

    fun setModule(module: SMVModule): DelayModuleBuilder {
        this.module = module
        return this
    }
}
