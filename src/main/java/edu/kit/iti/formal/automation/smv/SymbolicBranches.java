package edu.kit.iti.formal.automation.smv;

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
}
