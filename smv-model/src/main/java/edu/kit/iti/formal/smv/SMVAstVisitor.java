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

import edu.kit.iti.formal.smv.ast.SAssignment;
import edu.kit.iti.formal.smv.ast.*;
import edu.kit.iti.formal.smv.ast.SMVAst;
import edu.kit.iti.formal.smv.ast.SUnaryExpression;
import edu.kit.iti.formal.smv.ast.SVariable;

public interface SMVAstVisitor<T> {
    T visit(SMVAst top);

    T visit(SVariable v);

    T visit(SBinaryExpression be);

    T visit(SUnaryExpression ue);

    T visit(SLiteral l);

    T visit(SAssignment a);

    T visit(SCaseExpression ce);

    T visit(SMVModule smvModule);

    T visit(SFunction func);

    T visit(SQuantified quantified);

    T visit(SMVType.Module module);
}
