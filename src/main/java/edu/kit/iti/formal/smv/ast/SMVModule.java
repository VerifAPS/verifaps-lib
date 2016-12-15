package edu.kit.iti.formal.smv.ast;

import edu.kit.iti.formal.smv.SMVAstVisitor;

import java.util.List;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (11.12.16)
 */
public interface SMVModule {
    List<SVariable> getModuleParameter();

    /**
     *
     */
    List<SVariable> getInputVars();

    /**
     *
     */
    List<SVariable> getStateVars();

    List<SVariable> getFrozenVars();

    List<SMVExpr> getInvar();

    List<SMVExpr> getInvarSpec();

    List<SMVExpr> getLTLSpec();

    List<SMVExpr> getTrans();

    List<SMVExpr> getInit();

    List<SMVExpr> getCTLSpec();

    List<SAssignment> getInitAssignments();

    List<SAssignment> getNextAssignments();

    Map<SVariable, SMVExpr> getDefinitions();

    String getName();

    default
    public <T> T accept(SMVAstVisitor<T> visitor) {
        return visitor.visit(this);
    }

}
