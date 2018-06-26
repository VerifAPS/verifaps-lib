package edu.kit.iti.formal.automation.smv

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable

/**
 * Created by weigl on 27.11.16.
 */
data class SymbolicState(private val map: HashMap<SVariable, SMVExpr> = HashMap())
    : MutableMap<SVariable, SMVExpr> by map {
    constructor(m: Map<out SVariable, SMVExpr>) : this() {
        putAll(m)
    }

    operator fun get(x: String) = this[keys.find { it.name.equals(x, true) }]

    override fun toString(): String {
        val sb = StringBuffer()
        map.entries.joinTo(sb, prefix = "{", postfix = "}") { (k, v) ->
            "${k.name}=${v.repr()}"
        }
        return sb.toString()
    }
}
