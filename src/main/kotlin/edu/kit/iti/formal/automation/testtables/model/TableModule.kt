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
package edu.kit.iti.formal.automation.testtables.model


import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SVariable

import java.util.HashMap

/**
 * @author Alexander Weigl
 * @version 1 (11.12.16)
 */
class TableModule : SMVModule() {
    val clocks: Map<State, SVariable> = HashMap()

    override fun setName(name: String) {
        this.name = name
    }

    fun getStateVar(s: String): SVariable? {
        val ret: SVariable? = null
        for (v in stateVars)
            if (v.name == s) return v
        return null
    }
}
