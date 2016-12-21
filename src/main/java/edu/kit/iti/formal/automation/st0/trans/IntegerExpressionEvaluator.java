package edu.kit.iti.formal.automation.st0.trans;

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
