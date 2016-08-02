package edu.kit.iti.formal.automation.st.util;

import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.st.ast.*;

/**
 * Created by weigl on 10/07/14.
 */
public class AstVisitor<T> extends DefaultVisitor<T> {
    @Override
    public T defaultVisit(Visitable visitable) {
        return null;//throw new Error("not implemented for " + visitable.getClass());
    }


    @Override
    public T visit(AssignmentStatement assignmentStatement) {
        assignmentStatement.getExpression().visit(this);
        assignmentStatement.getLocation().visit(this);
        return null;
    }


    @Override
    public T visit(CaseConditions.Range range) {
        range.getStart().visit(this);
        range.getStop().visit(this);
        return null;
    }

    @Override
    public T visit(CaseConditions.IntegerCondition integerCondition) {
        integerCondition.getValue().visit(this);
        return null;
    }

    @Override
    public T visit(CaseConditions.Enumeration enumeration) {
        enumeration.getStart().visit(this);
        enumeration.getStop().visit(this);

        return null;

    }

    @Override
    public T visit(BinaryExpression binaryExpression) {
        binaryExpression.getLeftExpr().visit(this);
        binaryExpression.getRightExpr().visit(this);
        return null;
    }

    @Override
    public T visit(RepeatStatement repeatStatement) {
        repeatStatement.getCondition().visit(this);
        repeatStatement.getStatements().visit(this);
        return null;
    }

    @Override
    public T visit(WhileStatement whileStatement) {
        whileStatement.getCondition().visit(this);
        whileStatement.getStatements().visit(this);

        return null;
    }

    @Override
    public T visit(UnaryExpression unaryExpression) {
        unaryExpression.getExpression().visit(this);
        return null;
    }

    @Override
    public T visit(TypeDeclarations typeDeclarations) {
        for (TypeDeclaration td : typeDeclarations)
            td.visit(this);
        return null;
    }

    @Override
    public T visit(CaseStatement caseStatement) {
        caseStatement.getExpression().visit(this);
        for (CaseStatement.Case c : caseStatement.getCases())
            c.visit(this);

        caseStatement.getElseCase().visit(this);

        return null;
    }

    @Override
    public T visit(StatementList statements) {
        for (Statement s : statements)
            s.visit(this);
        return null;
    }

    @Override
    public T visit(ProgramDeclaration programDeclaration) {
        programDeclaration.getProgramBody().visit(this);
        programDeclaration.getScope().visit(this);
        return null;
    }

    @Override
    public T visit(ExpressionList expressions) {
        for (Expression e : expressions)
            e.visit(this);
        return null;
    }

    @Override
    public T visit(FunctionDeclaration functionDeclaration) {
        functionDeclaration.getScope().visit(this);
        functionDeclaration.getStatements().visit(this);
        return null;
    }

    @Override
    public T visit(ForStatement forStatement) {
        forStatement.getStart().visit(this);
        forStatement.getStep().visit(this);
        forStatement.getStop().visit(this);
        forStatement.getStatements().visit(this);
        return null;
    }

    @Override
    public T visit(FunctionBlockDeclaration functionBlockDeclaration) {
        functionBlockDeclaration.getFunctionBody().visit(this);
        functionBlockDeclaration.getScope().visit(this);
        return null;
    }


    @Override
    public T visit(IfStatement ifStatement) {
        for (GuardedStatement gs : ifStatement.getConditionalBranches())
            gs.visit(this);

        ifStatement.getElseBranch().visit(this);
        return null;
    }

    @Override
    public T visit(GuardedStatement guardedStatement) {
        guardedStatement.getCondition().visit(this);
        guardedStatement.getStatements().visit(this);
        return null;
    }

    @Override
    public T visit(CaseStatement.Case aCase) {
        aCase.getStatements().visit(this);
        for (CaseConditions c : aCase.getConditions())
            c.visit(this);
        return null;
    }

    @Override
    public T visit(VariableScope variableScope) {
        for (VariableDeclaration vd : variableScope.getVariableMap().values())
            vd.visit(this);
        return null;
    }

    @Override
    public T visit(VariableDeclaration variableDeclaration) {
        return super.visit(variableDeclaration);
    }
}
