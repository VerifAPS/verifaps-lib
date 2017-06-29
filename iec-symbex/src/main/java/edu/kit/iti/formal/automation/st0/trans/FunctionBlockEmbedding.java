package edu.kit.iti.formal.automation.st0.trans;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration;
import edu.kit.iti.formal.automation.st.ast.StatementList;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.automation.st0.STSimplifier;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

/**
 * @author Alexander Weigl
 * @version 1 (28.06.17)
 */
public class FunctbionBlockEmbbedder implements ST0Transformation {
    @Override
    public void transform(STSimplifier.State state) {
        for (FunctionBlockDeclaration fbd : state.functionBlocks.values()) {
            StatementList newStatements = embeddFunctionBlocks(fbd.getLocalScope(), fbd.getFunctionBody());
            fbd.setFunctionBody(newStatements);
        }

        for (VariableDeclaration vd : state.theProgram.getLocalScope().getLocalVariables().values()) {
            vd.setType(vd.getType() | STSimplifier.PROGRAM_VARIABLE);
        }

        state.theProgram.setProgramBody(embeddFunctionBlocks(state.theProgram.getLocalScope(),
                state.theProgram.getProgramBody()));
    }

    private StatementList embeddFunctionBlocks(LocalScope declared, StatementList statements) {
        Set<VariableDeclaration> decls =
                new HashSet<>(declared.getLocalVariables().values());
        for (VariableDeclaration vd : decls) {
            String typeName = vd.getDataTypeName();
            Any type = vd.getDataType();

            if (type instanceof FunctionBlockDataType) {
                FunctionBlockDataType fbdType = (FunctionBlockDataType) type;
                FunctionBlockDeclaration fbd = fbdType.getFunctionBlock();
                statements = embeddFunctionBlocksImpl(declared, statements, vd,
                        fbd);
            }
        }
        return statements;
    }


    private StatementList embeddFunctionBlocksImpl(LocalScope origin, StatementList intoStatements,
                                                   VariableDeclaration vd, FunctionBlockDeclaration fbd) {
        final String prefix = vd.getName() + "$";
        LocalScope embeddVariables = prefixNames(fbd.getLocalScope(), prefix);

        //declare new variables
        origin.getLocalVariables().putAll(embeddVariables.getLocalVariables());

        // remove FunctionBlock Instance
        origin.getLocalVariables().remove(vd.getName());

        //rename function
        Function<String, String> newName = (String s) -> {
            return prefix + s;
        };

        //Make a copy of the statements and add prefix to every variable
        VariableRenamer vr = new VariableRenamer(fbd.getFunctionBody(), newName);
        StatementList sl = vr.rename(); // <- this can be injected

        // inject into every function block call
        FunctionBlockEmbedder fbe = new FunctionBlockEmbedder(vd.getName(), sl, newName);
        return fbe.embedd(intoStatements);
    }

    private LocalScope prefixNames(LocalScope scope, String s) {
        LocalScope copy = scope.clone();
        for (VariableDeclaration nd : scope) {
            if (nd.isInput() || nd.isInOut() || nd.isOutput()) {
                int mask =
                        VariableDeclaration.INPUT |
                                VariableDeclaration.INOUT |
                                VariableDeclaration.OUTPUT;
                nd.setType((nd.getType() & ~mask) | VariableDeclaration.LOCAL);
            }
            nd.setName(s + nd.getName());
            copy.add(nd);
        }
        return copy;
    }

}
