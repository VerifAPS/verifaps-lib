package edu.kit.iti.formal.smv;

/*-
 * #%L
 * smv-model
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

import edu.kit.iti.formal.smv.ast.*;
import edu.kit.iti.formal.smv.parser.Facade;
import edu.kit.iti.formal.smv.parser.SMVParser;
import edu.kit.iti.formal.smv.parser.SMVTransformToAST;
import org.antlr.v4.runtime.CharStreams;
import org.jetbrains.annotations.NotNull;

import java.util.Arrays;
import java.util.List;
import java.util.function.BinaryOperator;

/**
 * Created by weigl on 26.11.16.
 */
public class SMVFacade {
    public static SFunction getFunction1(String name) {
        SFunction f = new SFunction(name);
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

    public static SMVExpr combine(SBinaryOperator op, List<SMVExpr> exprs, SMVExpr defaultValue) {
        return exprs.stream().reduce(reducer(op)).orElse(defaultValue);
    }

    public static BinaryOperator<SMVExpr> reducer(SBinaryOperator op) {
        return (SMVExpr a, SMVExpr b) -> {
            return new SBinaryExpression(a, op, b);
        };
    }

    public static SUnaryExpression NOT(SMVExpr e) {
        return new SUnaryExpression(SUnaryOperator.NEGATE, e);
    }

    public static SMVExpr expr(@NotNull String s) {
        SMVParser.ExprContext ctx = Facade.getParser(CharStreams.fromString(s)).expr();
        return (SMVExpr) ctx.accept(new SMVTransformToAST());
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
