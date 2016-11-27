package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.st.ast.CaseStatement;
import edu.kit.iti.formal.automation.st.util.Tuple;
import edu.kit.iti.formal.smv.SMV;
import edu.kit.iti.formal.smv.ast.SCaseExpression;
import edu.kit.iti.formal.smv.ast.SMVExpr;

import java.util.*;

/**
 * Created by weigl on 27.11.16.
 */
public class SymbolicBranches
        extends HashMap<String, SCaseExpression> {
    public void addBranch(SMVExpr condition, SymbolicState state) {
        for (Entry<String, SMVExpr> e : state.entrySet()) {
            get(e.getKey()).add(condition, e.getValue());
        }
    }

    @Override
    public SCaseExpression get(Object key) {
        SCaseExpression a = super.get(key);
        if (a != null)
            return a;
        a = new SCaseExpression();
        put(key.toString(), a);
        return a;
    }
}
