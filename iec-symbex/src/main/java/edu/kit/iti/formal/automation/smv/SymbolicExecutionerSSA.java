package edu.kit.iti.formal.automation.smv;

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

import edu.kit.iti.formal.automation.st.ast.AssignmentStatement;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (13.12.16)
 */
public class SymbolicExecutionerSSA extends SymbolicExecutioner {
    Map<SVariable, SMVExpr> definitions = new HashMap<>();
    Map<SVariable, Integer> counter = new HashMap<>();


    //TODO Test SSA construction
    @Override
    public SMVExpr visit(AssignmentStatement assign) {
        SymbolicState s = peek();
        SVariable var = lift((SymbolicReference) assign.getLocation());
        // save
        int c = counter.getOrDefault(var, 0);
        SVariable v = new SVariable(var + "__" + c + "_", null);
        definitions.put(v, assign.getExpression().accept(this));
        s.put(var, v);
        counter.put(var, ++c);
        return null;
    }
}
