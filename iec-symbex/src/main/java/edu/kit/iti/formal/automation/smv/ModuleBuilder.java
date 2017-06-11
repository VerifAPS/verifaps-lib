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

import edu.kit.iti.formal.automation.SymbExFacade;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration;
import edu.kit.iti.formal.automation.st.ast.TypeDeclarations;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.smv.ast.*;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class ModuleBuilder implements Runnable {

    private final ProgramDeclaration program;
    private final SymbolicState finalState;
    private final SMVModuleImpl module = new SMVModuleImpl();
    private final VariableDependency vardeps;
    //private Map<VariableDeclaration, SVariable> vars = new HashMap<>();

    public ModuleBuilder(ProgramDeclaration decl, TypeDeclarations types, SymbolicState ss) {
        finalState = ss;
        program = decl;
        vardeps = new VariableDependency(finalState);

    }

    public SMVModuleImpl getModule() {
        return module;
    }

    @Override
    public void run() {
        module.setName(program.getProgramName());

        Set<VariableDeclaration> outputVars =
                new HashSet<>(program.getLocalScope()
                        .filterByFlags(VariableDeclaration.OUTPUT));

        List<VariableDeclaration> inputVars =
                program.getLocalScope()
                        .filterByFlags(VariableDeclaration.INPUT);


        Set<SVariable> stateVariables = vardeps.dependsOn(outputVars, inputVars);

        insertVariables(stateVariables);
        insertInputVariables(inputVars);
    }

    private void insertInputVariables(List<VariableDeclaration> decls) {
        decls.stream()
                .map(SymbExFacade::asSVariable)
                .forEach(module.getModuleParameter()::add);
    }

    private void insertVariables(Set<SVariable> variables) {
        for (SVariable v : variables) {
            addVarDeclaration(v);
            addInitAssignment(v);
            addNextAssignment(v);
        }
    }

    private void addVarDeclaration(SVariable s) {
        module.getStateVars().add(s);
    }

    private void addInitAssignment(SVariable var) {
        VariableDeclaration s = program.getLocalScope().getVariable(var.getName());
        SMVExpr e;
        if (s.getInit() != null) {
            ScalarValue sv = (ScalarValue) s.getInit();
            e = (SMVExpr) sv.visit(new SymbolicExecutioner());
        } else {
            e = InitValue.INSTANCE.getInit(var.getSMVType());
        }
        SAssignment a = new SAssignment(var, e);
        module.getInitAssignments().add(a);
    }

    private void addNextAssignment(SVariable s) {
        SMVExpr e = finalState.get(s);
        SAssignment a = new SAssignment(s, e);
        module.getNextAssignments().add(a);
    }
}
