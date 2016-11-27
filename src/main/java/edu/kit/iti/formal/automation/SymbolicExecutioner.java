package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.exceptions.FunctionInvocationArgumentNumberException;
import edu.kit.iti.formal.automation.exceptions.FunctionUndefinedException;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.Tuple;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.smv.ast.*;

import java.util.*;

/**
 * Created by weigl on 26.11.16.
 */
public class SymbolicExecutioner extends DefaultVisitor<SMVExpr> {
    private SMVModule module;
    private GlobalScope globalScope;
    private LocalScope localScope;

    public SymbolicExecutioner() {
        push(new SymbolicState());
    }

    //region state handling
    private Stack<SymbolicState> state = new Stack<>();

    public SymbolicState peek() {
        return state.peek();
    }

    public SymbolicState pop() {
        return state.pop();
    }

    public void push() {
        push(new SymbolicState(peek()));
    }

    private <K, V> void push(SymbolicState map) {
        state.push(map);
    }
    //endregion

    //region rewriting of expressions using the current state
    @Override
    public SBinaryExpression visit(BinaryExpression binaryExpression) {
        SMVExpr left = binaryExpression.getLeftExpr().visit(this);
        SMVExpr right = binaryExpression.getRightExpr().visit(this);
        SBinaryOperator op = Utils.getSMVOperator(binaryExpression.getOperator());
        return new SBinaryExpression(left, op, right);
    }


    @Override
    public SUnaryExpression visit(UnaryExpression u) {
        SMVExpr left = u.getExpression().visit(this);
        SUnaryOperator op = Utils.getSMVOperator(u.getOperator());
        return new SUnaryExpression(op, left);
    }

    @Override
    public SMVExpr visit(SymbolicReference symbolicReference) {
        return peek().get(symbolicReference.getIdentifier());
    }

    @Override
    public SLiteral visit(ScalarValue<? extends Any, ?> tsScalarValue) {
        return Utils.asSMVLiteral(tsScalarValue);
    }


    //endregion

    @Override
    public SCaseExpression visit(ProgramDeclaration programDeclaration) {
        localScope = programDeclaration.getLocalScope();
        globalScope = localScope.getGlobalScope();
        push(new SymbolicState(localScope.getLocalVariables().size()));

        // initialize root state
        for (VariableDeclaration vd : localScope) {
            peek().put(vd.getName(), Utils.asSMVVariable(vd));
        }

        programDeclaration.getProgramBody().visit(this);
        return null;
    }

    @Override
    public SMVExpr visit(AssignmentStatement assign) {
        Map<String, SMVExpr> s = peek();
        String name = ((SymbolicReference) assign.getLocation()).getIdentifier();
        s.put(name, assign.getExpression().visit(this));
        return null;
    }

    @Override
    public SCaseExpression visit(StatementList statements) {
        for (Statement s : statements) {
            if (s instanceof ExitStatement) {
                return null;
            }
            s.visit(this);
        }
        return null;
    }


    @Override
    public SMVExpr visit(FunctionCall functionCall) {
        FunctionDeclaration fd = globalScope.resolveFunction(functionCall, localScope);
        if (fd != null) {
            //initialize data structure
            SymbolicState calleeState = new SymbolicState();
            SymbolicState callerState = peek();
            //region transfer variables
            List<FunctionCall.Parameter> parameters = functionCall.getParameters();
            List<VariableDeclaration> inputVars = fd.getLocalScope().filterByFlags(VariableDeclaration.INPUT);

            if (parameters.size() != inputVars.size()) {
                throw new FunctionInvocationArgumentNumberException();
            }

            for (int i = 0; i < parameters.size(); i++) {
                // name from definition, in order of declaration, expression from caller site
                String name = inputVars.get(i).getName();
                calleeState.put(name,
                        parameters.get(i).getExpression().visit(this));
            }
            push(calleeState);
            //endregion

            //region local variables (declaration and initialization)
            for (VariableDeclaration vd : fd.getLocalScope().getLocalVariables().values()) {
                if (!calleeState.containsKey(vd.getName())) {
                    TypeDeclaration td = vd.getTypeDeclaration();
                    if (td != null && td.getInitialization() != null) {
                        td.getInitialization().visit(this);
                    } else {
                        calleeState.put(vd.getName(), Utils.getDefaultValue(vd.getDataType()));
                    }
                }
            }
            //endregion

            // execution of body
            fd.getStatements().visit(this);
            pop();

            return calleeState.get(fd.getFunctionName());
        } else
            throw new FunctionUndefinedException();
    }

    @Override
    public SCaseExpression visit(IfStatement statement) {
        SymbolicBranches branchStates = new SymbolicBranches();

        for (GuardedStatement gs : statement.getConditionalBranches()) {
            SMVExpr condition = gs.getCondition().visit(this);
            push();
            gs.getStatements().visit(this);
            branchStates.addBranch(condition, pop());
        }

        if (statement.getElseBranch().size() > 0) {
            push();
            statement.getElseBranch().visit(this);
            branchStates.addBranch(SLiteral.TRUE, pop());
        }
        peek().putAll(branchStates);
        return null;
    }

    @Override
    public SCaseExpression visit(GuardedStatement guardedStatement) {
        return null;
    }
}
