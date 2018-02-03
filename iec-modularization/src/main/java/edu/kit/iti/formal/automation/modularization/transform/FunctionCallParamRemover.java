package edu.kit.iti.formal.automation.modularization.transform;

/*-
 * #%L
 * iec-modularization
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

import edu.kit.iti.formal.automation.modularization.StatementListModifier;
import edu.kit.iti.formal.automation.st.ast.AssignmentStatement;
import edu.kit.iti.formal.automation.st.ast.InvocationStatement;
import edu.kit.iti.formal.automation.st.ast.StatementList;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;

import java.util.ArrayList;

public final class FunctionCallParamRemover extends StatementListModifier {

    public FunctionCallParamRemover() {
        super(false);
    }

    public final StatementList visit(
            final InvocationStatement fbCallStmt) {

        assert fbCallStmt.getOutputParameters().size() == 0;

        final String prefix = fbCallStmt.getCalleeName() + "$";

        fbCallStmt.getInputParameters().forEach((param) -> _addToCurrentList(
                new AssignmentStatement(
                        new SymbolicReference(
                                prefix + param.getName()),
                        param.getExpression())));
        _addToCurrentList(fbCallStmt);

        fbCallStmt.setParameters(new ArrayList<>());
        return null;
    }
}
