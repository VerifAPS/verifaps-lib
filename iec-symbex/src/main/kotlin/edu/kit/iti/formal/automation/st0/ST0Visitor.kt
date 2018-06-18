package edu.kit.iti.formal.automation.st0

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
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.automation.visitors.DefaultVisitorNN

/**
 * @author Alexander Weigl (26.06.2014)
 * @version 1
 */
abstract class ST0Visitor<T> : DefaultVisitorNN<T>() {
    override fun visit(assignmentStatement: AssignmentStatement): T {
        return super.visit(assignmentStatement)
    }

    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration): T {
        return super.visit(enumerationTypeDeclaration)
    }

    override fun visit(unaryExpression: UnaryExpression): T {
        return super.visit(unaryExpression)
    }

    override fun visit(caseStatement: CaseStatement): T {
        return super.visit(caseStatement)
    }

    override fun visit(tsScalarValue: Literal): T {
        return super.visit(tsScalarValue)
    }

    override fun visit(symbolicReference: SymbolicReference): T {
        return super.visit(symbolicReference)
    }

    override fun visit(statements: StatementList): T {
        return super.visit(statements)
    }

    override fun visit(programDeclaration: ProgramDeclaration): T {
        return super.visit(programDeclaration)
    }

    override fun visit(invocation: Invocation): T {
        return super.visit(invocation)
    }

    override fun visit(ifStatement: IfStatement): T {
        return super.visit(ifStatement)
    }

    override fun visit(fbc: InvocationStatement): T {
        return super.visit(fbc)
    }

    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration): T {
        return super.visit(simpleTypeDeclaration)
    }
}
