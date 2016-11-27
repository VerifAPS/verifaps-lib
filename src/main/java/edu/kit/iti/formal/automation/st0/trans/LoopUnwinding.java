package edu.kit.iti.formal.automation.st0.trans;

import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstCopyVisitor;

/**
 * Created by weigl on 03/10/14.
 */
public class LoopUnwinding extends AstCopyVisitor {
    private LocalScope currentScope;

    public LoopUnwinding() {

    }

    @Override
    public Object visit(ProgramDeclaration programDeclaration) {
        currentScope = programDeclaration.getLocalScope();
        return super.visit(programDeclaration);
    }

    @Override
    public Object visit(FunctionDeclaration functionDeclaration) {
        currentScope = functionDeclaration.getLocalScope();
        return super.visit(functionDeclaration);
    }

    @Override
    public Object visit(FunctionBlockDeclaration functionBlockDeclaration) {
        currentScope = functionBlockDeclaration.getLocalScope();
        return super.visit(functionBlockDeclaration);
    }

    @Override
    public Object visit(ForStatement forStatement) {
        int start = (int) eval(forStatement.getStart());
        int stop = (int) eval(forStatement.getStop());

        int step = 1;
        if (forStatement.getStep() != null) {
            step = (int) eval(forStatement.getStep());
        }

        String var = forStatement.getVariable();

        StatementList sl = new StatementList();


        ExpressionReplacer er = new ExpressionReplacer();
        er.setStatements(forStatement.getStatements());
        SymbolicReference ref = new SymbolicReference(var);
        for (int i = start; i < stop; i += step) {
            er.getReplacements().put(
                    ref,
                    new ScalarValue<>(AnyInt.INT, i)
            );
            sl.addAll(er.replace());
        }
        return sl;
    }

    private long eval(Expression expr) {
        IntegerExpressionEvaluator iee = new IntegerExpressionEvaluator(currentScope);
        return (long) expr.visit(iee);
    }
}
