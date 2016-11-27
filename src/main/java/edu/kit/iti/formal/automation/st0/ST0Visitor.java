package edu.kit.iti.formal.automation.st0;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;

/**
 * @author weigla
 * @date 26.06.2014
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
    public T visit(ScalarValue<? extends Any, ?> tsScalarValue) {
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
    public T visit(FunctionCallStatement functionCallStatement) {
        return super.visit(functionCallStatement);
    }

    @Override
    public T visit(SimpleTypeDeclaration simpleTypeDeclaration) {
        return super.visit(simpleTypeDeclaration);
    }
}
