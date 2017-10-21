package edu.kit.iti.formal.automation.smv;

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

import edu.kit.iti.formal.automation.exceptions.FunctionInvocationArgumentNumberException;
import edu.kit.iti.formal.automation.exceptions.FunctionUndefinedException;
import edu.kit.iti.formal.automation.exceptions.UnknownDatatype;
import edu.kit.iti.formal.automation.exceptions.UnknownVariableException;
import edu.kit.iti.formal.automation.operators.Operators;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.smv.translators.*;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.smv.SMVFacade;
import edu.kit.iti.formal.smv.ast.*;
import lombok.Getter;
import lombok.Setter;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

/**
 * Created by weigl on 26.11.16.
 */
public class SymbolicExecutioner extends DefaultVisitor<SMVExpr> {
    private GlobalScope globalScope = GlobalScope.defaultScope();
    private LocalScope localScope = new LocalScope(globalScope);
    private Map<String, SVariable> varCache = new HashMap<>();

    @Getter
    @Setter
    private OperationMap operationMap = new DefaultOperationMap();

    @Getter
    @Setter
    private TypeTranslator typeTranslator = new DefaultTypeTranslator();

    @Getter
    @Setter
    private ValueTranslator valueTranslator = new DefaultValueTranslator();

    @Getter
    @Setter
    private InitValueTranslator initValueTranslator = new DefaultInitValue();

    //region state handling
    private Stack<SymbolicState> state = new Stack<>();
    private Expression caseExpression;

    public SymbolicExecutioner() {
        push(new SymbolicState());
    }

    //region getter and setters
    public GlobalScope getGlobalScope() {
        return globalScope;
    }

    public void setGlobalScope(GlobalScope globalScope) {
        this.globalScope = globalScope;
    }
    //endregion

    public LocalScope getLocalScope() {
        return localScope;
    }

    public void setLocalScope(LocalScope localScope) {
        this.localScope = localScope;
    }

    public SymbolicState peek() {
        return state.peek();
    }

    public SymbolicState pop() {
        return state.pop();
    }

    public void push() {
        push(new SymbolicState(peek()));
    }
    //endregion

    public <K, V> void push(SymbolicState map) {
        state.push(map);
    }

    public SVariable lift(VariableDeclaration vd) {
        try {
            if (vd.getDataType() == null) {
                vd.setDataType(localScope.getGlobalScope()
                        .resolveDataType(vd.getDataTypeName()));
            }
            if (!varCache.containsKey(vd))
                varCache.put(vd.getName(), typeTranslator.translate(vd));
            return varCache.get(vd.getName());
        } catch (NullPointerException e) {
            throw new UnknownDatatype("Datatype not given/inferred for variable "
                    + vd.getName(), e);
        }
    }

    public SVariable lift(SymbolicReference vd) {
        if (varCache.containsKey(vd.getIdentifier()))
            return varCache.get(vd.getIdentifier());
        else
            throw new UnknownVariableException("Variable access to not declared variable" + vd);
    }

    //region rewriting of expressions using the current state
    @Override
    public SMVExpr visit(BinaryExpression binaryExpression) {
        SMVExpr left = binaryExpression.getLeftExpr().accept(this);
        SMVExpr right = binaryExpression.getRightExpr().accept(this);
        return operationMap
                .translateBinaryOperator(left, binaryExpression.getOperator(),
                        right);
    }

    @Override
    public SMVExpr visit(UnaryExpression u) {
        SMVExpr left = u.getExpression().accept(this);
        return operationMap.translateUnaryOperator(u.getOperator(), left);
    }

    @Override
    public SMVExpr visit(SymbolicReference symbolicReference) {
        return peek().get(lift(symbolicReference));
    }

    //endregion

    @Override
    public SLiteral visit(Literal literal) {
        return valueTranslator.translate(literal);
    }

    @Override
    public SCaseExpression visit(ProgramDeclaration programDeclaration) {
        localScope = programDeclaration.getLocalScope();
        globalScope = localScope.getGlobalScope();
        push(new SymbolicState(localScope.getLocalVariables().size()));

        // initialize root state
        for (VariableDeclaration vd : localScope) {
            SVariable s = lift(vd);
            peek().put(s, s);
        }

        programDeclaration.getProgramBody().accept(this);
        return null;
    }

    @Override
    public SMVExpr visit(AssignmentStatement assign) {
        SymbolicState s = peek();
        s.put(lift((SymbolicReference) assign.getLocation()),
                assign.getExpression().accept(this));
        return null;
    }

    @Override
    public SCaseExpression visit(StatementList statements) {
        for (Statement s : statements) {
            if (s instanceof ExitStatement) {
                return null;
            }
            s.accept(this);
        }
        return null;
    }

    @Override
    public SMVExpr visit(InvocationStatement fbc) {
        return visit(fbc.getInvocation());
    }

    @Override
    public SMVExpr visit(Invocation invocation) {
        FunctionDeclaration fd = globalScope.resolveFunction(invocation, localScope);
        if (fd == null)
            throw new FunctionUndefinedException(invocation);


        //initialize data structure
        SymbolicState calleeState = new SymbolicState();
        SymbolicState callerState = peek();

        //region register function name as output variable
        if (null == fd.getLocalScope().getVariable(fd.getFunctionName())
                && fd.getReturnType() != null) {
            fd.getLocalScope().builder()
                    .setBaseType(fd.getReturnTypeName())
                    .push(VariableDeclaration.OUTPUT)
                    .identifiers(fd.getFunctionName())
                    .create();
        }
        //endregion

        //region local variables (declaration and initialization)
        for (VariableDeclaration vd : fd.getLocalScope().getLocalVariables().values()) {
            if (!calleeState.containsKey(vd.getName())) {
                TypeDeclaration td = vd.getTypeDeclaration();
                if (td != null && td.getInitialization() != null) {
                    td.getInitialization().accept(this);
                } else {

                    calleeState.put(lift(vd),
                            valueTranslator.translate(
                                    initValueTranslator.getInit(vd.getDataType())));
                }
            }
        }
        //endregion

        //region transfer variables
        List<Invocation.Parameter> parameters = invocation.getParameters();
        List<VariableDeclaration> inputVars = fd.getLocalScope().filterByFlags(VariableDeclaration.INPUT);

        if (parameters.size() != inputVars.size()) {
            throw new FunctionInvocationArgumentNumberException();
        }

        for (int i = 0; i < parameters.size(); i++) {
            // name from definition, in order of declaration, expression from caller site
            calleeState.put(lift(inputVars.get(i)),
                    parameters.get(i).getExpression().accept(this));
        }
        push(calleeState);
        //endregion

        // execution of body
        fd.getStatements().accept(this);
        pop();

        return calleeState.get(lift(fd.getLocalScope().getVariable(fd.getFunctionName())));
    }

    @Override
    public SCaseExpression visit(IfStatement statement) {
        SymbolicBranches branchStates = new SymbolicBranches();

        for (GuardedStatement gs : statement.getConditionalBranches()) {
            SMVExpr condition = gs.getCondition().accept(this);
            push();
            gs.getStatements().accept(this);
            branchStates.addBranch(condition, pop());
        }

        push();
        statement.getElseBranch().accept(this);
        branchStates.addBranch(SLiteral.TRUE, pop());

        peek().putAll(branchStates.asCompressed());
        return null;
    }

    @Override
    public SMVExpr visit(CaseStatement caseStatement) {
        SymbolicBranches branchStates = new SymbolicBranches();

        for (CaseStatement.Case gs : caseStatement.getCases()) {
            SMVExpr condition = buildCondition(caseStatement.getExpression(), gs);
            push();
            gs.getStatements().accept(this);
            branchStates.addBranch(condition, pop());
        }

        push();
        caseStatement.getElseCase().accept(this);
        branchStates.addBranch(SLiteral.TRUE, pop());

        peek().putAll(branchStates.asCompressed());
        return null;
    }

    private SMVExpr buildCondition(Expression e, CaseStatement.Case c) {
        caseExpression = e;
        return c.getConditions()
                .stream()
                .map(a -> a.accept(this))
                .reduce(SMVFacade.reducer(SBinaryOperator.OR)).get();
    }

    @Override
    public SMVExpr visit(CaseCondition.Range r) {
        BinaryExpression lower = new BinaryExpression(caseExpression, r.getStart(), Operators.GREATER_EQUALS);
        BinaryExpression upper = new BinaryExpression(r.getStop(), caseExpression, Operators.GREATER_EQUALS);
        BinaryExpression and = new BinaryExpression(lower, upper, Operators.AND);
        return and.accept(this);
    }

    @Override
    public SMVExpr visit(CaseCondition.IntegerCondition i) {
        BinaryExpression be = new BinaryExpression(caseExpression, i.getValue(), Operators.EQUALS);
        return be.accept(this);
    }


    @Override
    public SMVExpr visit(CaseCondition.Enumeration e) {
        BinaryExpression be = new BinaryExpression(caseExpression, e.getStart(), Operators.EQUALS);
        return be.accept(this);
        //TODO rework case conditions
    }
}
