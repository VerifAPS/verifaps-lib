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

import edu.kit.iti.formal.smv.printers.StringPrinter;
import edu.kit.iti.formal.smv.SMVAstVisitor;
import lombok.Data;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/************************************************************/

/**
 *
 */
@Data
public class SMVModule extends SMVAst {
    /**
     *
     */
    protected List<SVariable> inputVars = new ArrayList<>();
    protected List<SVariable> moduleParameters = new ArrayList<>();
    /**
     *
     */
    protected List<SVariable> stateVars = new ArrayList<>();
    /**
     *
     */
    protected List<SVariable> frozenVars = new ArrayList<>();

    protected List<SAssignment> init = new ArrayList<>();
    protected List<SMVExpr> invariants = new ArrayList<>();
    protected List<SMVExpr> invariantSpecs = new ArrayList<>();
    protected List<SMVExpr> ltlSpec = new ArrayList<>();
    protected List<SMVExpr> ctlSpec = new ArrayList<>();
    protected List<SAssignment> next = new ArrayList<>();
    protected String name = "";
    protected List<SMVExpr> transExpr = new ArrayList<>();
    protected List<SMVExpr> initExpr = new ArrayList<>();
    private Map<SVariable, SMVExpr> definitions = new HashMap<>();

    public <T> T accept(SMVAstVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public String toString() {
        return StringPrinter.toString(this);
    }

    public List<SAssignment> getNextAssignments() {
        return next;
    }

    public List<SAssignment> getInitAssignments() {
        return init;
    }

}

