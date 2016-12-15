package edu.kit.iti.formal.automation.smv;

import edu.kit.iti.formal.automation.SymbExFacade;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.st.ast.Initialization;
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration;
import edu.kit.iti.formal.automation.st.ast.TypeDeclarations;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.smv.ast.*;

import java.util.*;
import java.util.function.Consumer;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class ModuleBuilder implements Runnable {

    private final ProgramDeclaration program;
    private final SymbolicState finalState;
    private final SMVModuleImpl module = new SMVModuleImpl();
    private final VariableDependency vardeps;
    private Map<VariableDeclaration, SVariable> vars = new HashMap<>();

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
        module.setName(program.getBlockName());

        Set<VariableDeclaration> outputVars =
                new HashSet<>(program.getLocalScope()
                        .filterByFlags(VariableDeclaration.OUTPUT));

        List<VariableDeclaration> inputVars =
                program.getLocalScope()
                        .filterByFlags(VariableDeclaration.INPUT);


        Set<String> variables = vardeps.dependsOn(outputVars);
        variables.stream()
                .filter(v -> !program.getLocalScope().getVariable(v).isInput())
                .map(v -> program.getLocalScope().getVariable(v))
                .forEach(outputVars::add);

        insertVariables(outputVars);
        insertInputVariables(inputVars);
    }

    private void insertInputVariables(List<VariableDeclaration> decls) {
        decls.stream()
                .map(SymbExFacade::asSVariable)
                .forEach(module.getModuleParameter()::add);
    }

    private void insertVariables(Collection<VariableDeclaration> variables) {
        for (VariableDeclaration v : variables) {
            addVarDeclaration(v);
            addInitAssignment(v);
            addNextAssignment(v);
        }
    }

    private void addVarDeclaration(VariableDeclaration s) {
        SMVType type = s.getDataType().accept(DataTypeTranslator.INSTANCE);
        SVariable var = new SVariable(s.getName(), type);
        module.getStateVars().add(var);
        vars.put(s, var);
    }

    private void addInitAssignment(VariableDeclaration s) {

        SMVExpr e;
        if (s.getInit() != null) {
            ScalarValue sv = (ScalarValue) s.getInit();
            e = (SMVExpr) sv.visit(new SymbolicExecutioner());
        } else {
            e = InitValue.INSTANCE.getInit(vars.get(s).getSMVType());
        }
        SAssignment a = new SAssignment(vars.get(s), e);
        module.getInitAssignments().add(a);
    }

    private void addNextAssignment(VariableDeclaration s) {
        SMVExpr e = finalState.get(SymbExFacade.asSVariable(s));
        SAssignment a = new SAssignment(vars.get(s), e);
        module.getNextAssignments().add(a);
    }
}
