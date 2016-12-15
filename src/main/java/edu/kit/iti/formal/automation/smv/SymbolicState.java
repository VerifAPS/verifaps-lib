package edu.kit.iti.formal.automation.smv;

import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by weigl on 27.11.16.
 */
public class SymbolicState extends HashMap<SVariable, SMVExpr> {

    public SymbolicState(int initialCapacity, float loadFactor) {
        super(initialCapacity, loadFactor);
    }

    public SymbolicState(int initialCapacity) {
        super(initialCapacity);
    }

    public SymbolicState() {
    }

    public SymbolicState(Map<? extends SVariable, ? extends SMVExpr> m) {
        super(m);
    }
}
