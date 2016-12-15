package edu.kit.iti.formal.smv;

import edu.kit.iti.formal.smv.ast.*;

import java.util.Arrays;
import java.util.List;
import java.util.function.BinaryOperator;

/**
 * Created by weigl on 26.11.16.
 */
public class SMVFacade {
    public static SFunction getFunction1(String name) {
        SFunction f = new SFunction(name, null);
        f.setTypeSolver(FunctionTypeSolvers.FIRST_ARGUMENT);
        return f;
    }

    public static SMVExpr next(SMVExpr expr) {
        return new SFunction("next", expr);
    }


    public static SMVExpr caseexpr(SMVExpr... exprs) {
        SCaseExpression e = new SCaseExpression();
        for (int i = 0; i < exprs.length; i += 2) {
            e.addCase(exprs[i], exprs[i + 1]);
        }
        return e;
    }


    public static SMVExpr combine(SBinaryOperator op, SMVExpr... exprs) {
        return Arrays.stream(exprs).reduce(reducer(op)).get();
    }

    public static SMVExpr combine(SBinaryOperator op, List<SMVExpr> exprs) {
        return exprs.stream().reduce(reducer(op)).get();
    }

    public static BinaryOperator<SMVExpr> reducer(SBinaryOperator op) {
        return (SMVExpr a, SMVExpr b) -> {
            return new SBinaryExpression(a, op, b);
        };
    }

    public static SUnaryExpression NOT(SMVExpr e) {
        return new SUnaryExpression(SUnaryOperator.NEGATE, e);
    }

/*
    public static CaseExpression makeIfThenElse(Expression cond, Expression thenExpr, Expression elseExpr) {
        CaseExpression result = new CaseExpression();
        result.addCase(cond, thenExpr);
        result.setElseExpression(elseExpr);
        return result;
    }
*/

}
