package edu.kit.iti.formal.smv.ast;

/*-
 * #%L
 * smv-model
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

import edu.kit.iti.formal.smv.Printer;
import edu.kit.iti.formal.smv.SMVAstVisitor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/************************************************************/

/**
 *
 */
public class SMVModule extends SMVAst {
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

    
    public List<SVariable> getModuleParameter() {
        return moduleParameters;
    }

    
    public List<SVariable> getInputVars() {
        return inputvars;
    }

    
    public List<SVariable> getStateVars() {
        return statevars;
    }

    
    public List<SVariable> getFrozenVars() {
        return frozenvars;
    }

    
    public List<SMVExpr> getInvar() {
        return invariants;
    }

    
    public List<SMVExpr> getInvarSpec() {
        return invariantspecs;
    }

    
    public List<SMVExpr> getLTLSpec() {
        return ltlspec;
    }

    
    public List<SMVExpr> getTrans() {
        return transexpr;
    }

    
    public List<SMVExpr> getInit() {
        return initexpr;
    }

    
    public List<SMVExpr> getCTLSpec() {
        return ctlspec;
    }

    
    public List<SAssignment> getInitAssignments() {
        return init;
    }

    
    public List<SAssignment> getNextAssignments() {
        return next;
    }

    
    public Map<SVariable, SMVExpr> getDefinitions() {
        return definitions;
    }

    
    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    
    public <T> T accept(SMVAstVisitor<T> visitor) {
        return visitor.visit((SMVModule) this);
    }

    public String toString() {
        return Printer.toString(this);
    }
}

