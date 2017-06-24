package edu.kit.iti.formal.smv;

/*-
 * #%L
 * smv-model
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

/**
 * @author Alexander Weigl
 * @version 1 (12.06.17)
 */
public class SMVAstDefaultVisitor<T> implements SMVAstVisitor<T> {
    private T defaultVisit(SMVAst top) {
        return null;
    }

    @Override
    public T visit(SMVAst top) {
        return defaultVisit(top);
    }

    @Override
    public T visit(SVariable v) {
        return defaultVisit(v);
    }

    @Override
    public T visit(SBinaryExpression be) {
        return defaultVisit(be);
    }

    @Override
    public T visit(SUnaryExpression ue) {
        return defaultVisit(ue);
    }

    @Override
    public T visit(SLiteral l) {
        return defaultVisit(l);
    }

    @Override
    public T visit(SAssignment a) {
        return defaultVisit(a);
    }

    @Override
    public T visit(SCaseExpression ce) {
        return defaultVisit(ce);
    }

    @Override
    public T visit(SMVModule smvModule) {
        return null;//return defaultVisit(smvModule);
    }

    @Override
    public T visit(SFunction func) {
        return defaultVisit(func);
    }

    @Override
    public T visit(SQuantified quantified) {
        return defaultVisit(quantified);
    }
}
