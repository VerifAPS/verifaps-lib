package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.smv.DataTypeTranslator;
import edu.kit.iti.formal.automation.smv.ModuleBuilder;
import edu.kit.iti.formal.automation.smv.SymbolicExecutioner;
import edu.kit.iti.formal.automation.smv.SymbolicState;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st0.STSimplifier;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SMVModule;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.Arrays;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public final class SymbExFacade {
    public static final SMVExpr evaluateFunction(
            FunctionDeclaration decl, SMVExpr... args) {
        return evaluateFunction(decl, Arrays.asList(args));

    }

    private static SMVExpr evaluateFunction(FunctionDeclaration decl, List<SMVExpr> ts) {
        SymbolicExecutioner se = new SymbolicExecutioner();
        SymbolicState state = new SymbolicState();
        // <name>(i1,i2,i2,...)
        FunctionCall fc = new FunctionCall();
        fc.setFunctionName(decl.getFunctionName());
        int i = 0;
        for (VariableDeclaration vd : decl.getLocalScope().filterByFlags(VariableDeclaration.INPUT)) {
            fc.getParameters().add(
                    new FunctionCall.Parameter(vd.getName(),
                            false,
                            new SymbolicReference(vd.getName())));
            state.put(se.lift(vd), ts.get(i++));
        }
        se.push(state);
        se.getGlobalScope().registerFunction(decl);
        return fc.visit(se);
    }

    /**
     * @param elements
     * @return
     */
    public static final TopLevelElements simplify(TopLevelElements elements) {
        STSimplifier stSimplifier = new STSimplifier(elements);
        stSimplifier.transform();
        return stSimplifier.getProcessed();
    }

    public static final SMVModule evaluateProgram(TopLevelElements elements) {
        TopLevelElements a = simplify(elements);
        return evaluateProgram((ProgramDeclaration) a.get(1), (TypeDeclarations) a.get(0));
    }

    public static final SMVModule evaluateProgram(ProgramDeclaration decl, TypeDeclarations types) {
        SymbolicExecutioner se = new SymbolicExecutioner();
        decl.visit(se);
        ModuleBuilder moduleBuilder = new ModuleBuilder(decl, types, se.peek());
        moduleBuilder.run();
        return moduleBuilder.getModule();
    }

    public static final SVariable asSVariable(VariableDeclaration vd) {
        return new SVariable(vd.getName(),
                vd.getDataType().accept(DataTypeTranslator.INSTANCE)
        );
    }
}
