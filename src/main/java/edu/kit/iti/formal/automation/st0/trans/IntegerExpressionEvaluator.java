package edu.kit.iti.formal.automation.st0.trans;

import edu.kit.iti.formal.automation.Console;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.operators.BinaryOperator;
import edu.kit.iti.formal.automation.operators.Operators;
import edu.kit.iti.formal.automation.operators.UnaryOperator;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstVisitor;

/**
 * Created by weigl on 03/10/14.
 */
public class IntegerExpressionEvaluator extends AstVisitor<Long> {
    private LocalScope scope;

    public IntegerExpressionEvaluator(LocalScope scope) {
        this.scope = scope;
    }

    @Override
    public Long visit(BinaryExpression binaryExpression) {
        BinaryOperator op = binaryExpression.getOperator();

        long left = binaryExpression.getLeftExpr().visit(this);
        long right = binaryExpression.getRightExpr().visit(this);

        if (op == Operators.ADD)
            return left + right;
        if (op == Operators.DIV)
            return left / right;
        if (op == Operators.SUB)
            return left - right;
        if (op == Operators.MULT)
            return left * right;

        Console.error("Unsupported operation %s", op);
        return left;
    }

    @Override
    public Long visit(UnaryExpression unaryExpression) {
        UnaryOperator op = unaryExpression.getOperator();
        long left = unaryExpression.getExpression().visit(this);

        if (op == Operators.MINUS)
            return -left;

        Console.error("Unsupported operation %s", op);
        return left;
    }

    @Override
    public Long visit(ScalarValue<? extends Any, ?> tsScalarValue) {
        long r = 0;
        if (tsScalarValue.getValue() instanceof Integer) {
            return (long) ((int) ((Integer) tsScalarValue.getValue()));
        } else {
            return (Long) tsScalarValue.getValue();
        }
    }

    @Override
    public Long visit(SymbolicReference symbolicReference) {
        String id = symbolicReference.getIdentifier();
        VariableDeclaration vd = scope.getVariable(symbolicReference);
        ScalarValue sv = (ScalarValue) vd.getInit();
        try {
            return (Long) sv.getValue();
        } catch (ClassCastException e) {
            Console.error("%s is not a integer variable", id);
            return 0L;
        }
    }
}
