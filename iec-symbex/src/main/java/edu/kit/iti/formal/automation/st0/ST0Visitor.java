package edu.kit.iti.formal.automation.st0;

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;

/**
 * @author Alexander Weigl (26.06.2014)
 * @version 1
 */
public abstract class ST0Visitor<T> extends DefaultVisitor<T> {
    @Override
    public T visit(AssignmentStatement assignmentStatement) {
        return super.visit(assignmentStatement);
    }

    @Override
    public T visit(EnumerationTypeDeclaration enumerationTypeDeclaration) {
        return super.visit(enumerationTypeDeclaration);
    }

    @Override
    public T visit(UnaryExpression unaryExpression) {
        return super.visit(unaryExpression);
    }

    @Override
    public T visit(CaseStatement caseStatement) {
        return super.visit(caseStatement);
    }

    @Override
    public T visit(Literal tsScalarValue) {
        return super.visit(tsScalarValue);
    }

    @Override
    public T visit(SymbolicReference symbolicReference) {
        return super.visit(symbolicReference);
    }

    @Override
    public T visit(StatementList statements) {
        return super.visit(statements);
    }

    @Override
    public T visit(ProgramDeclaration programDeclaration) {
        return super.visit(programDeclaration);
    }

    @Override
    public T visit(FunctionCall functionCall) {
        return super.visit(functionCall);
    }

    @Override
    public T visit(IfStatement ifStatement) {
        return super.visit(ifStatement);
    }

    @Override
    public T visit(FunctionBlockCallStatement fbc) {
        return super.visit(fbc);
    }

    @Override
    public T visit(SimpleTypeDeclaration simpleTypeDeclaration) {
        return super.visit(simpleTypeDeclaration);
    }
}
