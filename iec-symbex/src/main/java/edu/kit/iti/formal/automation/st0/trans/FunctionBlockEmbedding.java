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

import com.google.errorprone.annotations.Var;
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
public class FunctionBlockEmbedding implements ST0Transformation {
    @Override
    public void transform(STSimplifier.State state) {
        for (FunctionBlockDeclaration fbd : state.functionBlocks.values()) {
            StatementList newStatements = embeddFunctionBlocks(fbd.getLocalScope(), fbd.getFunctionBody());
            fbd.setFunctionBody(newStatements);
        }

        for (VariableDeclaration vd : state.theProgram.getLocalScope().getLocalVariables().values()) {
            vd.setType(vd.getType() | STSimplifier.PROGRAM_VARIABLE);
        }

        state.theProgram.setProgramBody(
                embeddFunctionBlocks(state.theProgram.getLocalScope(),
                                     state.theProgram.getProgramBody()));
    }

    private StatementList embeddFunctionBlocks(LocalScope declared, StatementList statements) {
        Set<VariableDeclaration> decls = new HashSet<>(declared.getLocalVariables().values());
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
        assert !intoStatements.isEmpty();
        final String prefix = vd.getName() + "$";
        //rename function
        Function<String, String> newName = (String s) -> {
            return prefix + s;
        };

        LocalScope embeddVariables = prefixNames(fbd.getLocalScope(), newName);

        //declare new variables
        origin.getLocalVariables().putAll(embeddVariables.getLocalVariables());

        // remove FunctionBlock Instance
        origin.getLocalVariables().remove(vd.getName());

        //Make a copy of the statements and add prefix to every variable
        VariableRenamer vr = new VariableRenamer(fbd.getFunctionBody(), newName);
        StatementList sl = vr.rename(); // <- this can be injected

        // inject into every function block call
        FunctionBlockEmbedder fbe = new FunctionBlockEmbedder(vd.getName(), sl, newName);
        return fbe.embedd(intoStatements);
    }

    private LocalScope prefixNames(LocalScope scope, Function<String, String> newName) {
        LocalScope copy = new LocalScope().copy();
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

}
