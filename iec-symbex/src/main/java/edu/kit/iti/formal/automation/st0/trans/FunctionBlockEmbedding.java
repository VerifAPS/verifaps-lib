package edu.kit.iti.formal.automation.st0.trans;

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.datatypes.AnyDt;
import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.st0.STSimplifier;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.RequiredArgsConstructor;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * @author Alexander Weigl
 * @version 1 (28.06.17)
 */
public class FunctionBlockEmbedding implements ST0Transformation {
    @Override
    public void transform(STSimplifier.State state) {
        for (VariableDeclaration vd : state.theProgram.getScope()) {
            vd.setType(vd.getType() | STSimplifier.PROGRAM_VARIABLE);
        }

        CodeWithScope cws = new CodeWithScope(state.theProgram);
        state.theProgram.setStBody(embeddFunctionBlocks(cws));
    }

    /**
     * first embedds the variables for each function block
     */
    private StatementList embeddFunctionBlocks(CodeWithScope outer) {
        Set<VariableDeclaration> decls = new HashSet<>(outer.scope.asMap().values());
        ActionEmbedder ae = new ActionEmbedder(outer);
        outer.statements = ae.embedd();

        for (VariableDeclaration vd : decls) {
            AnyDt type = vd.getDataType();
            if (type instanceof FunctionBlockDataType) {
                FunctionBlockDataType fbdType = (FunctionBlockDataType) type;
                FunctionBlockDeclaration fbd = fbdType.getFunctionBlock();
                CodeWithScope inner = new CodeWithScope(fbd);
                outer.statements = embeddFunctionBlocksImpl(outer, vd, inner);
            }
        }
        return outer.statements;
    }


    private StatementList embeddFunctionBlocksImpl(CodeWithScope outer, VariableDeclaration instance, CodeWithScope inner) {
        assert !outer.statements.isEmpty();

        //recursive call:
        StatementList toBeEmbedded = embeddFunctionBlocks(inner);

        final String prefix = instance.getName() + "$";
        //rename function
        Function<String, String> newName = (String s) -> {
            return prefix + s;
        };

        Scope embeddVariables = prefixNames(inner.scope, newName);

        //declare new variables
        outer.scope.addVariables(embeddVariables);

        // remove FunctionBlock Instance
        outer.scope.asMap().remove(instance.getName());

        //Make a copy of the statements and add prefix to every variable
        VariableRenamer vr = new VariableRenamer(toBeEmbedded.copy(), newName);
        StatementList prefixedStatements = vr.rename(); // <- this can be injected

        // inject into every function block call
        FunctionBlockEmbedder fbe = FunctionBlockEmbedder.builder()
                .instanceName(instance.getName())
                .toEmbedd(prefixedStatements)
                .renameVariable(newName)
                .build();


        inner.actions.forEach((n, s) -> {
                    //TODO strange that I do not need a variable renaming here
                    //VariableRenamer v = new VariableRenamer(s, newName);
                    fbe.getActions().put(n, s); // <- this can be injected
                }
        );

        return fbe.embedd(outer.statements);
    }

    private Scope prefixNames(Scope scope, Function<String, String> newName) {
        Scope copy = new Scope().copy();
        for (VariableDeclaration vd : scope) {
            VariableDeclaration nd = vd.copy();
            if (nd.isInput() || nd.isInOut() || nd.isOutput()) {
                int mask =
                        VariableDeclaration.INPUT |
                                VariableDeclaration.INOUT |
                                VariableDeclaration.OUTPUT;
                nd.setType((nd.getType() & ~mask) | VariableDeclaration.LOCAL);
            }
            nd.setName(newName.apply(nd.getName()));
            copy.add(nd);
        }
        return copy;
    }

    @Builder
    @AllArgsConstructor
    public static class CodeWithScope {
        Scope scope;
        StatementList statements;
        @Builder.Default
        Map<String, StatementList> actions = new HashMap<>();

        public CodeWithScope(ProgramDeclaration theProgram) {
            scope = theProgram.getScope();
            statements = theProgram.getStBody().copy();
            theProgram.getActions().forEach((k, v) -> actions.put(k, v.getStBody()));
        }

        public CodeWithScope(FunctionBlockDeclaration fbd) {
            scope = fbd.getScope();
            statements = fbd.getStBody().copy();
            fbd.getActions().forEach((k, v) -> actions.put(k, v.getStBody()));
        }

    }

    @RequiredArgsConstructor
    private class ActionEmbedder extends AstMutableVisitor {
        final CodeWithScope cws;

        public StatementList embedd() {
            return (StatementList) cws.statements.accept(this);
        }

        @Override
        public Object visit(InvocationStatement fbc) {
            //TODO this should be done via the scope.
            // One place to rule function resolving!
            if (cws.actions.containsKey(fbc.getCalleeName())) {
                StatementList statements = new StatementList(cws.actions.get(fbc.getCalleeName()));
                statements.add(0, CommentStatement.single("Call of action: %s", fbc.getCalleeName()));
                statements.add(CommentStatement.single("End of action call: %s", fbc.getCalleeName()));
                return statements;
            }
            return super.visit(fbc);
        }
    }
}
