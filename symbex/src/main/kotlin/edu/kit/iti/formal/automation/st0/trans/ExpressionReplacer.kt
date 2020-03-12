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

import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import java.util.HashMap

/**
 * Created by weigl on 03/10/14.
 *
 * @author Alexander Weigl
 */
class ExpressionReplacer(var statements: StatementList) : AstVisitor<Any>() {
    var replacements: MutableMap<Expression, Expression> = HashMap()

    override fun defaultVisit(obj: Any) = error("not implemented for $obj")


    override fun visit(symbolicReference: SymbolicReference): Any {
        return if (replacements.containsKey(symbolicReference)) {
            replacements[symbolicReference]!!
        } else super.visit(symbolicReference)!!
    }

    override fun visit(unaryExpression: UnaryExpression): Any {
        return if (replacements.containsKey(unaryExpression)) {
            replacements[unaryExpression]!!
        } else super.visit(unaryExpression)!!
    }

    override fun visit(binaryExpression: BinaryExpression): Any {
        return if (replacements.containsKey(binaryExpression)) {
            replacements[binaryExpression]!!
        } else super.visit(binaryExpression)!!
    }

    fun replace(): Collection<Statement> {
        return statements!!.accept(this) as StatementList
    }
}
