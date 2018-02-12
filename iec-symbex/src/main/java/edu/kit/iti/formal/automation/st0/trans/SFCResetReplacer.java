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

import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import edu.kit.iti.formal.automation.st.util.Statements;
import edu.kit.iti.formal.automation.visitors.Visitable;
import org.antlr.v4.runtime.CommonToken;

/**
 * Created by weigl on 28/10/14.
 */
public class SFCResetReplacer extends AstMutableVisitor {
    public static ST0Transformation getTransformation() {
        return state -> {
            SFCResetReplacer srr = new SFCResetReplacer();
            state.theProgram = (ProgramDeclaration) state.theProgram.accept(srr);
        };
    }

    @Override
    public Object defaultVisit(Visitable visitable) {
        return visitable;
    }

    @Override
    public Object visit(AssignmentStatement assignmentStatement) {
        try {
            SymbolicReference sr = (SymbolicReference) assignmentStatement.getLocation();
            Expression expression = assignmentStatement.getExpression();

            if (sr.getIdentifier() != null && sr.getIdentifier()
                    .endsWith("$SFCReset")) {
                return Statements.ifthen(
                        expression,
                        new AssignmentStatement(
                                new SymbolicReference(sr.getIdentifier().replace("SFCReset", "_state")),
                                Literal.enumerate(new CommonToken(-1, "Init"))
                        ));
            }
        } catch (ClassCastException e) {
        }
        return super.visit(assignmentStatement);
    }
}
