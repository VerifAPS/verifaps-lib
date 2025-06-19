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
package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.ast.EnumLit
import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.Literal
import edu.kit.iti.formal.automation.st.ast.SymbolicReference
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import java.util.*

object RewriteEnums : AstMutableVisitor() {
    private var lastScope: Scope? = null

    override fun visit(localScope: Scope): Scope {
        lastScope = localScope
        return localScope
    }

    override fun visit(literal: Literal): Expression {
        when (literal) {
            is EnumLit -> literal.value = literal.value.uppercase(Locale.getDefault())
            else -> {}
        }
        return literal
    }

    override fun visit(symbolicReference: SymbolicReference): Expression {
        val scope = lastScope
        if (scope != null) {
            val value = symbolicReference.identifier
            if (scope.resolveVariable(symbolicReference) == null) {
                val enum0 = scope.resolveEnumByValue(value)
                if (enum0 != null) return EnumLit(RefTo(enum0), value.uppercase(Locale.getDefault()))

                val enum1 = scope.resolveEnum(value)
                if (enum1 != null && symbolicReference.hasSub()) {
                    return EnumLit(RefTo(enum1), symbolicReference.sub!!.identifier.uppercase(Locale.getDefault()))
                }
            }
        }
        return symbolicReference
    }
}