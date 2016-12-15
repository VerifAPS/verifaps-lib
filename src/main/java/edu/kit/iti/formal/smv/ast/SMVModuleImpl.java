package edu.kit.iti.formal.smv.ast;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.formal.smv.Printer;
import edu.kit.iti.formal.smv.SMVAstVisitor;

/************************************************************/

/**
 *
 */
public class SMVModuleImpl extends SMVAst implements SMVModule {
    /**
     *
     */
    protected List<SVariable> inputvars = new ArrayList<>();
    protected List<SVariable> moduleParameters = new ArrayList<>();
    /**
     *
     */
    protected List<SVariable> statevars = new ArrayList<>();
    /**
     *
     */
    protected List<SVariable> frozenvars = new ArrayList<>();

    protected List<SAssignment> init = new ArrayList<>();
    protected List<SMVExpr> invariants = new ArrayList<>();
    protected List<SMVExpr> invariantspecs = new ArrayList<>();
    protected List<SMVExpr> ltlspec = new ArrayList<>();
    protected List<SMVExpr> ctlspec = new ArrayList<>();
    protected List<SAssignment> next = new ArrayList<>();
    protected String name = "";
    protected List<SMVExpr> transexpr = new ArrayList<>();
    protected List<SMVExpr> initexpr = new ArrayList<>();
    private Map<SVariable, SMVExpr> definitions = new HashMap<>();

    @Override
    public List<SVariable> getModuleParameter() {
        return moduleParameters;
    }

    @Override
    public List<SVariable> getInputVars() {
        return inputvars;
    }

    @Override
    public List<SVariable> getStateVars() {
        return statevars;
    }

    @Override
    public List<SVariable> getFrozenVars() {
        return frozenvars;
    }

    @Override
    public List<SMVExpr> getInvar() {
        return invariants;
    }

    @Override
    public List<SMVExpr> getInvarSpec() {
        return invariantspecs;
    }

    @Override
    public List<SMVExpr> getLTLSpec() {
        return ltlspec;
    }

    @Override
    public List<SMVExpr> getTrans() {
        return transexpr;
    }

    @Override
    public List<SMVExpr> getInit() {
        return initexpr;
    }

    @Override
    public List<SMVExpr> getCTLSpec() {
        return ctlspec;
    }

    @Override
    public List<SAssignment> getInitAssignments() {
        return init;
    }

    @Override
    public List<SAssignment> getNextAssignments() {
        return next;
    }

    @Override
    public Map<SVariable, SMVExpr> getDefinitions() {
        return definitions;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public <T> T accept(SMVAstVisitor<T> visitor) {
        return visitor.visit((SMVModule) this);
    }

    public void setName(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return Printer.toString(this);
    }
}

