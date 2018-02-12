/*
 * #%L
 * iec61131lang
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

package edu.kit.iti.formal.automation.st0.trans;

import edu.kit.iti.formal.automation.datatypes.RecordType;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import edu.kit.iti.formal.automation.st0.STSimplifier;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.AllArgsConstructor;
import lombok.Data;
import org.jetbrains.annotations.NotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Augusto Modanese
 */
@Data
public class StructEmbedding implements ST0Transformation {
    private STSimplifier.State state;

    @Override
    public void transform(@NotNull STSimplifier.State state) {
        this.state = state;
        process(state.functions.values());
        process(state.theProgram);
    }

    private void process(@NotNull Collection<? extends TopLevelElement> topLevelElements) {
        topLevelElements.forEach(this::process);
    }

    private void process(@NotNull TopLevelElement topLevelElement) {
        StructEmbeddingVisitor structEmbeddingVisitor = new StructEmbeddingVisitor();
        topLevelElement.accept(structEmbeddingVisitor);
        for (Visitor renameVisitor : structEmbeddingVisitor.renameVisitors) {
            state.functions.values().forEach(f -> f.accept(renameVisitor));
            state.theProgram.accept(renameVisitor);
        }
    }

    private static class StructEmbeddingVisitor extends AstVisitor {
        final List<Visitor> renameVisitors = new ArrayList<>();

        @Override
        public Object visit(@NotNull Scope localScope) {
            for (VariableDeclaration v : new ArrayList<>(localScope.stream()
                    .filter(v -> v.getDataType() instanceof RecordType)
                    .collect(Collectors.toList()))) {
                RecordType struct = (RecordType) v.getDataType();
                struct.getFields().forEach(field -> localScope.add(createStructVariable(field, v)));
                renameVisitors.add(new StructRenameVisitor(v.getName(), struct));
                localScope.asMap().remove(v.getName());
            }
            return super.visit(localScope);
        }

        @NotNull
        private VariableDeclaration createStructVariable(@NotNull RecordType.Field field,
                                                         @NotNull VariableDeclaration structVariable) {
            StructureInitialization initialization =
                    (StructureInitialization) structVariable.getTypeDeclaration().getInitialization();
            VariableDeclaration newVariable =
                    new VariableDeclaration(structVariable.getName() + "$" + field.getName(),
                            structVariable.getType(),
                            field.getDataType());
            newVariable.getTypeDeclaration().setBaseType(field.getDataType());
            newVariable.getTypeDeclaration().setBaseTypeName(field.getDataType().getName());
            if (initialization != null)
                newVariable.getTypeDeclaration().setInitialization(initialization.getInitValues().get(field.getName()));
            return newVariable;
        }
    }

    @AllArgsConstructor
    private static class StructRenameVisitor extends AstMutableVisitor {
        @NotNull
        private final String structName;

        @NotNull
        private final RecordType structType;

        @Override
        public Object visit(@NotNull Invocation invocation) {
            for (Invocation.Parameter parameter : new ArrayList<>(invocation.getParameters())) {
                if (parameter.getExpression() instanceof SymbolicReference) {
                    SymbolicReference symbolicReference = (SymbolicReference) parameter.getExpression();
                    if (symbolicReference.getIdentifier().equals(structName) && !symbolicReference.hasSub()) {
                        // Found structure being passed as parameter
                        invocation.getParameters().remove(parameter);
                        for (RecordType.Field field : structType.getFields())
                            invocation.addParameter(new Invocation.Parameter(
                                    parameter.getName() != null
                                            ? parameter.getName() + "$" + field.getName()
                                            : null,
                                    parameter.isOutput(),
                                    new SymbolicReference(structName + "$" + field.getName())));
                    }
                }
            }
            return super.visit(invocation);
        }

        @Override
        public Object visit(@NotNull SymbolicReference symbolicReference) {
            if (symbolicReference.getIdentifier().equals(structName) && symbolicReference.hasSub())
                return new SymbolicReference(structName + "$" + symbolicReference.getSub().getIdentifier());
            return super.visit(symbolicReference);
        }
    }
}
