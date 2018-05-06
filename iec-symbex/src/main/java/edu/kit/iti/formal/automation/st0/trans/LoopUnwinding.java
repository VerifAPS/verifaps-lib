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

import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.visitors.Visitable;

/**
 * Created by weigl on 03/10/14.
 */
public class LoopUnwinding extends AstMutableVisitor {
    public LoopUnwinding() {

    }

    public static ST0Transformation getTransformation() {
        return state -> {
            LoopUnwinding loopUnwinding = new LoopUnwinding();
            state.theProgram = (ProgramDeclaration) state.theProgram.accept(loopUnwinding);
        };
    }

    @Override
    public Object defaultVisit(Visitable visitable) {
        return visitable;
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
                    ref, Literal.integer(i));
            sl.addAll(er.replace());
        }
        return sl;
    }

    private long eval(Expression expr) {
        IntegerExpressionEvaluator iee = new IntegerExpressionEvaluator(currentScope);
        return (long) expr.accept(iee);
    }
}
