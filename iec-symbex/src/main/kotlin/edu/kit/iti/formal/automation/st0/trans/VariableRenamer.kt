package edu.kit.iti.formal.automation.st0.trans

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

import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.StatementList
import edu.kit.iti.formal.automation.st.ast.SymbolicReference
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor

/**
 * @author Alexander Weigl (26.06.2014)
 */
class VariableRenamer(
        private val isGlobal: (SymbolicReference) -> Boolean,
        private val statements: StatementList?,
        private val newName: (String) -> String)
    : AstMutableVisitor() {

    override fun visit(symbolicReference: SymbolicReference): Expression {
        if (!isGlobal(symbolicReference)) {
            val name = newName(symbolicReference.identifier)
            val ref = SymbolicReference(name, symbolicReference.sub)
            ref.subscripts = symbolicReference.sub?.subscripts
            return ref
        }
        return symbolicReference
    }

    fun rename(): StatementList {
        return if (statements != null)
            statements.accept(this) as StatementList
        else
            StatementList()
    }
}
