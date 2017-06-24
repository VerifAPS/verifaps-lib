package edu.kit.iti.formal.automation.st.util;

/*-
 * #%L
 * iec61131lang
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
import edu.kit.iti.formal.automation.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.automation.visitors.Visitable;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * <p>AstMutableVisitor class.</p>
 *
 * @author weigla (26.06.2014)
 *         This visitors defines all function with go down and setting the results of visit as the new value.
 *         Not copying datastructures.
 */
public class AstMutableVisitor extends DefaultVisitor<Object> {
    /**
     * {@inheritDoc}
     */
    @Override
    public Object defaultVisit(Visitable visitable) {
        System.out.println("AstTransform.defaultVisit");
        System.err.println(("maybe not fully and right supported " + visitable.getClass()));
        return visitable;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(AssignmentStatement assignmentStatement) {
        assignmentStatement.setExpression((Expression) assignmentStatement.getExpression().visit(this));
        assignmentStatement.setLocation((Reference) assignmentStatement.getLocation().visit(this));
        return assignmentStatement;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseCondition.IntegerCondition integerCondition) {
        ScalarValue sv = (ScalarValue) integerCondition.getValue().<Object>visit(this);
        integerCondition.setValue(sv);
        return integerCondition;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseCondition.Enumeration enumeration) {
        enumeration.setStart((ScalarValue<EnumerateType, String>) enumeration.getStart().<Object>visit(this));
        enumeration.setStop((ScalarValue<EnumerateType, String>) enumeration.getStop().<Object>visit(this));
        return enumeration;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(BinaryExpression binaryExpression) {
        binaryExpression.setLeftExpr(
                (Expression) binaryExpression.getLeftExpr().<Object>visit(this));

        binaryExpression.setRightExpr(
                (Expression) binaryExpression.getRightExpr().<Object>visit(this));

        return binaryExpression;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(UnaryExpression unaryExpression) {
        unaryExpression.setExpression((Expression) unaryExpression.getExpression().<Object>visit(this));
        return unaryExpression;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(RepeatStatement repeatStatement) {
        repeatStatement.setCondition((Expression) repeatStatement.getCondition().<Object>visit(this));
        repeatStatement.setStatements((StatementList) repeatStatement.getStatements().<Object>visit(this));
        return repeatStatement;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(WhileStatement whileStatement) {
        whileStatement.setCondition((Expression) whileStatement.getCondition().<Object>visit(this));
        whileStatement.setStatements((StatementList) whileStatement.getStatements().<Object>visit(this));
        return whileStatement;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseStatement caseStatement) {
        LinkedList<CaseStatement.Case> l = new LinkedList<>();
        for (CaseStatement.Case c : caseStatement.getCases()) {
            l.add((CaseStatement.Case) c.visit(this));
        }

        caseStatement.setCases(l);

        caseStatement.setExpression((Expression) caseStatement.getExpression().visit(this));
        caseStatement.setElseCase((StatementList) caseStatement.getElseCase().visit(this));
        return caseStatement;
    }


    /*
    @Override
    public Object visit(SymbolicReference symbolicReference) {

        if (symbolicReference.getSub() != null)
            symbolicReference.setSub((Reference) symbolicReference.getSub().<Object>visit(this));

        if (symbolicReference.getSubscripts() != null)
            symbolicReference.setSubscripts((ExpressionList)
                    symbolicReference.getSubscripts().<Object>visit(this));

        return symbolicReference;
    }*/

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(StatementList statements) {
        StatementList r = new StatementList();
        for (Statement s : statements) {
            r.add((Statement) s.visit(this));
        }
        return r;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        programDeclaration.setLocalScope((LocalScope) programDeclaration.getLocalScope().visit(this));
        programDeclaration.setProgramBody((StatementList) programDeclaration.getProgramBody().visit(this));
        return programDeclaration;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ScalarValue<? extends Any, ?> tsScalarValue) {
        return tsScalarValue;
        //return new ScalarValue<>(tsScalarValue.getDataType(), tsScalarValue.getValue());
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(FunctionCall functionCall) {
        List<Expression> list = new ArrayList<>();
        list.addAll(functionCall.getParameters());
        functionCall.setParameters(list);
        return functionCall;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ForStatement forStatement) {
        forStatement.setStart((Expression) forStatement.getStart().visit(this));
        forStatement.setStatements((StatementList) forStatement.getStatements().visit(this));
        forStatement.setStep((Expression) forStatement.getStep().visit(this));
        forStatement.setStop((Expression) forStatement.getStop().visit(this));
        return forStatement;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(IfStatement i) {
        LinkedList<GuardedStatement> guards = new LinkedList<>();
        for (GuardedStatement gc : i.getConditionalBranches()) {
            guards.add((GuardedStatement) gc.visit(this));
        }
        i.setConditionalBranches(guards);
        i.setElseBranch((StatementList) i.getElseBranch().visit(this));
        return i;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CommentStatement commentStatement) {
        return commentStatement;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(GuardedStatement guardedStatement) {
        guardedStatement.setCondition((Expression) guardedStatement.getCondition().visit(this));
        guardedStatement.setStatements((StatementList) guardedStatement.getStatements().visit(this));
        return guardedStatement;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(FunctionBlockCallStatement fbc) {
        fbc.getParameters().stream()
                .forEach(p -> p.setExpression((Expression) p.getExpression().visit(this)));
        return fbc;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseStatement.Case aCase) {
        List<CaseCondition> v = this.<CaseCondition>visitList(aCase.getConditions());
        aCase.setConditions(v);
        aCase.setStatements((StatementList) aCase.getStatements().visit(this));
        return aCase;
    }

    private <T> List<T> visitList(List<? extends Visitable> list) {
        List l = new ArrayList();
        for (Visitable v : list)
            l.add((T) v.visit(this));
        return l;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ArrayTypeDeclaration arrayTypeDeclaration) {
        return arrayTypeDeclaration;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ExitStatement exitStatement) {
        return exitStatement;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseCondition.Range range) {
        range.setStart((ScalarValue) range.getStart().visit(this));
        range.setStop((ScalarValue) range.getStop().visit(this));
        return super.visit(range);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ConfigurationDeclaration configurationDeclaration) {
        return configurationDeclaration;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(LocalScope localScope) {
        return localScope;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(VariableDeclaration variableDeclaration) {
        variableDeclaration.setTypeDeclaration(
                (TypeDeclaration<?>)
                        variableDeclaration.getTypeDeclaration().visit(this));

        return variableDeclaration;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ArrayInitialization initializations) {
        return initializations;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(EnumerationTypeDeclaration enumerationTypeDeclaration) {
        return enumerationTypeDeclaration;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(TypeDeclarations typeDeclarations) {
        TypeDeclarations td = new TypeDeclarations();
        for (TypeDeclaration t : typeDeclarations)
            td.add((TypeDeclaration) td.visit(this));
        return td;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ExpressionList expressions) {
        ExpressionList expressionList = new ExpressionList();
        for (Expression e : expressions)
            expressionList.add((Expression) e.visit(this));
        return expressionList;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        functionDeclaration.setLocalScope((LocalScope) functionDeclaration.getLocalScope().visit(this));
        functionDeclaration.setStatements((StatementList) functionDeclaration.getStatements().visit(this));
        return functionDeclaration;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ResourceDeclaration resourceDeclaration) {
        return resourceDeclaration;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        functionBlockDeclaration.setLocalScope((LocalScope) functionBlockDeclaration.getLocalScope().visit(this));
        functionBlockDeclaration.setFunctionBody((StatementList) functionBlockDeclaration.getFunctionBody().visit(this));
        return functionBlockDeclaration;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ReturnStatement returnStatement) {
        return returnStatement;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(StringTypeDeclaration stringTypeDeclaration) {
        return stringTypeDeclaration;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(StructureTypeDeclaration structureTypeDeclaration) {
        return structureTypeDeclaration;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(SubRangeTypeDeclaration subRangeTypeDeclaration) {
        return subRangeTypeDeclaration;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(SimpleTypeDeclaration simpleTypeDeclaration) {
        return simpleTypeDeclaration;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(StructureInitialization structureInitialization) {
        return structureInitialization;
    }
}
