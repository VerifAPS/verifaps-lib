package edu.kit.iti.formal.automation.rvt

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

import edu.kit.iti.formal.smv.ast.SCaseExpression
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable

import java.util.concurrent.ConcurrentHashMap


/**
 * Created by weigl on 27.11.16.
 */
class SymbolicBranches : ConcurrentHashMap<SVariable, SCaseExpression>() {
    fun addBranch(condition: SMVExpr, state: SymbolicState) {
        for ((key, value) in state) {
            get(key)?.add(condition, value)
        }
    }

    override operator fun get(key: SVariable): SCaseExpression? {
        var a: SCaseExpression? = super.get(key)
        if (a != null)
            return a
        a = SCaseExpression()
        put(key as SVariable, a)
        return a
    }

    /**
     *
     */
    fun asCompressed(): SymbolicState {
        val sb = SymbolicState()
        entries.parallelStream().forEach { entry -> sb[entry.key] = entry.value.compress() }
        return sb
    }
}
