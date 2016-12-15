package edu.kit.iti.formal.automation.smv;

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
        definitions.put(v, assign.getExpression().visit(this));
        s.put(var, v);
        counter.put(var, ++c);
        return null;
    }
}
