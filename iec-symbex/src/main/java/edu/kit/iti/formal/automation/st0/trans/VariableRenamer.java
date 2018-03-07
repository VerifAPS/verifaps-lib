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

import edu.kit.iti.formal.automation.st.ast.StatementList;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;

import java.util.function.Function;

/**
 * @author Alexander Weigl (26.06.2014)
 */
public class VariableRenamer extends AstMutableVisitor {
    private final StatementList statements;
    private final Function<String, String> newName;

    public VariableRenamer(StatementList functionBody, Function<String, String> newName) {
        //assert !functionBody.isEmpty();
        this.newName = newName;
        statements = functionBody;
    }

    @Override
    public Object visit(SymbolicReference symbolicReference) {
        String name = newName.apply(symbolicReference.getIdentifier());
        SymbolicReference ref = new SymbolicReference(name, symbolicReference.getSub());
        ref.setSubscripts(symbolicReference.getSubscripts());
        return ref;
    }

    public StatementList rename() {
        if (statements != null)
            return (StatementList) statements.accept(this);
        else
            return new StatementList();
    }
}
