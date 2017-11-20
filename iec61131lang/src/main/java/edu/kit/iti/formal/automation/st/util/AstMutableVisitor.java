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

import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.Visitable;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * <p>AstMutableVisitor class.</p>
 * This visitors defines all function with go down and setting the results of accept as the new value.
 * Not copying datastructures.
 *
 * @author Alexander Weigl (26.06.2014)
 */
public class AstMutableVisitor extends AstVisitor<Object> {
    /**
     * {@inheritDoc}
     */
    @Override
    public Object defaultVisit(Visitable visitable) {
        //System.out.println("AstTransform.defaultVisit");
        //System.err.println(("maybe not fully and right supported " + visitable.getClass()));
        return visitable;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(AssignmentStatement assignmentStatement) {
        assignmentStatement.setExpression((Expression) assignmentStatement.getExpression().accept(this));
        assignmentStatement.setLocation((Reference) assignmentStatement.getLocation().accept(this));
        return assignmentStatement;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseCondition.IntegerCondition integerCondition) {
        Literal sv = (Literal) integerCondition.getValue().accept(this);
        integerCondition.setValue(sv);
        return integerCondition;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseCondition.Enumeration enumeration) {
        enumeration.setStart((Literal) enumeration.getStart().accept(this));
        enumeration.setStop((Literal) enumeration.getStop().accept(this));
        return enumeration;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(BinaryExpression binaryExpression) {
        binaryExpression.setLeftExpr(
                (Expression) binaryExpression.getLeftExpr().accept(this));

        binaryExpression.setRightExpr(
                (Expression) binaryExpression.getRightExpr().accept(this));

        return binaryExpression;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(UnaryExpression unaryExpression) {
        unaryExpression.setExpression((Expression) unaryExpression.getExpression().accept(this));
        return unaryExpression;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(RepeatStatement repeatStatement) {
        repeatStatement.setCondition((Expression) repeatStatement.getCondition().accept(this));
        repeatStatement.setStatements((StatementList) repeatStatement.getStatements().accept(this));
        return repeatStatement;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(WhileStatement whileStatement) {
        whileStatement.setCondition((Expression) whileStatement.getCondition().accept(this));
        whileStatement.setStatements((StatementList) whileStatement.getStatements().accept(this));
        return whileStatement;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseStatement caseStatement) {
        LinkedList<CaseStatement.Case> l = new LinkedList<>();
        for (CaseStatement.Case c : caseStatement.getCases()) {
            l.add((CaseStatement.Case) c.accept(this));
        }

        caseStatement.setCases(l);

        caseStatement.setExpression((Expression) caseStatement.getExpression().accept(this));
        caseStatement.setElseCase((StatementList) caseStatement.getElseCase().accept(this));
        return caseStatement;
    }


    /*
    @Override
    public Object accept(SymbolicReference symbolicReference) {

        if (symbolicReference.getSub() != null)
            symbolicReference.setSub((Reference) symbolicReference.getSub().accept(this));

        if (symbolicReference.getSubscripts() != null)
            symbolicReference.setSubscripts((ExpressionList)
                    symbolicReference.getSubscripts().accept(this));

        return symbolicReference;
    }*/

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(StatementList statements) {
        StatementList r = new StatementList();
        for (Statement s : statements) {
            if (s == null) continue;
            r.add((Statement) s.accept(this));
        }
        return r;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        programDeclaration.setLocalScope((LocalScope) programDeclaration.getLocalScope().accept(this));
        programDeclaration.setProgramBody((StatementList) programDeclaration.getProgramBody().accept(this));
        return programDeclaration;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(Invocation invocation) {
        invocation.setCallee((SymbolicReference) invocation.getCallee().accept(this));
        invocation.setParameters(invocation.getParameters().stream()
                .map(p -> (Invocation.Parameter) p.accept(this)).collect(Collectors.toList()));
        return invocation;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ForStatement forStatement) {
        forStatement.setStart((Expression) forStatement.getStart().accept(this));
        forStatement.setStatements((StatementList) forStatement.getStatements().accept(this));
        forStatement.setStep((Expression) forStatement.getStep().accept(this));
        forStatement.setStop((Expression) forStatement.getStop().accept(this));
        return forStatement;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(IfStatement i) {
        LinkedList<GuardedStatement> guards = new LinkedList<>();
        for (GuardedStatement gc : i.getConditionalBranches()) {
            guards.add((GuardedStatement) gc.accept(this));
        }
        i.setConditionalBranches(guards);
        i.setElseBranch((StatementList) i.getElseBranch().accept(this));
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
        guardedStatement.setCondition((Expression) guardedStatement.getCondition().accept(this));
        guardedStatement.setStatements((StatementList) guardedStatement.getStatements().accept(this));
        return guardedStatement;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(InvocationStatement fbc) {
        fbc.setInvocation((Invocation) fbc.getInvocation().accept(this));
        return fbc;
    }

    @Override
    public Object visit(Invocation.Parameter parameter) {
        parameter.setExpression((Expression) parameter.getExpression().accept(this));
        return parameter;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(CaseStatement.Case aCase) {
        List<CaseCondition> v = this.visitList(aCase.getConditions());
        aCase.setConditions(v);
        aCase.setStatements((StatementList) aCase.getStatements().accept(this));
        return aCase;
    }

    private <T> List<T> visitList(List<? extends Visitable> list) {
        List l = new ArrayList();
        for (Visitable v : list)
            l.add(v.accept(this));
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
        range.setStart((Literal) range.getStart().accept(this));
        range.setStop((Literal) range.getStop().accept(this));
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
                        variableDeclaration.getTypeDeclaration().accept(this));

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
            td.add((TypeDeclaration) t.accept(this));
        return td;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(ExpressionList expressions) {
        ExpressionList expressionList = new ExpressionList();
        for (Expression e : expressions)
            expressionList.add((Expression) e.accept(this));
        return expressionList;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        functionDeclaration.setLocalScope((LocalScope) functionDeclaration.getLocalScope().accept(this));
        functionDeclaration.setStatements((StatementList) functionDeclaration.getStatements().accept(this));
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
        functionBlockDeclaration.setFunctionBody((StatementList) functionBlockDeclaration.getFunctionBody().accept(this));
        return visit((ClassDeclaration) functionBlockDeclaration);
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
        return super.visit(simpleTypeDeclaration);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public Object visit(StructureInitialization structureInitialization) {
        return super.visit(structureInitialization);
    }

    @Override
    public Object visit(Location location) {
        return super.visit(location);
    }

    @Override
    public Object visit(Deref deref) {
        return super.visit(deref);
    }

    @Override
    public Object visit(SymbolicReference symbolicReference) {
        return super.visit(symbolicReference);
    }

    @Override
    public Object visit(PointerTypeDeclaration ptd) {
        return super.visit(ptd);
    }

    @Override
    public Object visit(IdentifierInitializer init) {
        return super.visit(init);
    }

    @Override
    public Object visit(ClassDeclaration clazz) {
        clazz.setLocalScope((LocalScope) clazz.getLocalScope().accept(this));

        List<MethodDeclaration> methods = new ArrayList<>(clazz.getMethods().size());
        for (MethodDeclaration method : clazz.getMethods()) {
            methods.add((MethodDeclaration) method.accept(this));
        }
        clazz.setMethods(methods);

        return super.visit(clazz);
    }

    @Override
    public Object visit(MethodDeclaration method) {
        method.setLocalScope((LocalScope) method.getLocalScope().accept(this));
        method.setStatements((StatementList) method.getStatements().accept(this));
        return super.visit(method);
    }

    @Override
    public Object visit(InterfaceDeclaration interfaceDeclaration) {
        List<MethodDeclaration> methods = new ArrayList<>(interfaceDeclaration.getMethods().size());
        for (MethodDeclaration method : interfaceDeclaration.getMethods()) {
            MethodDeclaration newMethod = (MethodDeclaration) method.accept(this);
            if (newMethod != null)
                methods.add(method);
        }
        interfaceDeclaration.setMethods(methods);
        return super.visit(interfaceDeclaration);
    }

    @Override
    public Object visit(GlobalVariableListDeclaration globalVariableListDeclaration) {
        globalVariableListDeclaration.setLocalScope((LocalScope) visit(globalVariableListDeclaration.getLocalScope()));
        return super.visit(globalVariableListDeclaration);
    }

    @Override
    public Object visit(Literal literal) {
        return super.visit(literal);
    }
}
