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

import edu.kit.iti.formal.automation.st.ast.AssignmentStatement
import edu.kit.iti.formal.automation.st.ast.SymbolicReference
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable

import java.util.HashMap

/**
 * @author Alexander Weigl
 * @version 1 (13.12.16)
 */
class SymbolicExecutionerSSA : SymbolicExecutioner() {
    internal var definitions: MutableMap<SVariable, SMVExpr> = HashMap()
    internal var counter: MutableMap<SVariable, Int> = HashMap()

    //TODO Test SSA construction
    override fun visit(assign: AssignmentStatement): SMVExpr? {
        val s = peek()
        val `var` = lift(assign.location as SymbolicReference)
        // save
        var c = (counter as java.util.Map<SVariable, Int>).getOrDefault(`var`, 0)
        val v = SVariable(`var`.toString() + "__" + c + "_", null!!)
        definitions[v] = assign.expression.accept(this)!!
        s[`var`] = v
        counter[`var`] = ++c
        return null
    }
}
