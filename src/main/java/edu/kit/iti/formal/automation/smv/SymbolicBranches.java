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

import edu.kit.iti.formal.smv.ast.SCaseExpression;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.*;


/**
 * Created by weigl on 27.11.16.
 */
public class SymbolicBranches
        extends HashMap<SVariable, SCaseExpression> {
    public void addBranch(SMVExpr condition, SymbolicState state) {
        for (Entry<SVariable, SMVExpr> e : state.entrySet()) {
            get(e.getKey()).add(condition, e.getValue());
        }
    }

    @Override
    public SCaseExpression get(Object key) {
        SCaseExpression a = super.get(key);
        if (a != null)
            return a;
        a = new SCaseExpression();
        put((SVariable) key, a);
        return a;
    }

    /**
     *
     */
    public SymbolicState asCompressed() {
        SymbolicState sb = new SymbolicState();
        forEach((key, value) -> sb.put(key, value.compress()));
        return sb;
    }
}
