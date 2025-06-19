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
package edu.kit.iti.formal.stvs.model.expressions

import edu.kit.iti.formal.stvs.model.common.FreeVariable
import edu.kit.iti.formal.stvs.model.common.IoVariable
import java.util.regex.Pattern

/**
 * Runtime-representation for variables in [Expression]s.
 * At this point it is not known whether this is a reference to a [FreeVariable] or an
 * [IoVariable]; it is simply the String name of either of those.
 *
 * @author Philipp
 */
data class VariableExpr(val variableName: String?, val index: Int? = null) : Expression() {
    override fun <R> accept(visitor: ExpressionVisitor<R>): R = visitor.visitVariable(this)

    fun equals(expr: VariableExpr): Boolean = variableName == expr.variableName

    override fun toString(): String {
        val indexStr = index?.let { "[$it]" } ?: ""
        return "VariableExpr($variableName$indexStr)"
    }

    companion object {
        @JvmField
        val IDENTIFIER_PATTERN: Pattern = Pattern.compile("[a-zA-Z_][\$a-zA-Z0-9_]*")
    }
}