/*
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

package edu.kit.iti.formal.automation.stoo.trans;

import edu.kit.iti.formal.automation.datatypes.AnyDt;
import edu.kit.iti.formal.automation.datatypes.ClassDataType;
import edu.kit.iti.formal.automation.datatypes.InterfaceDataType;
import edu.kit.iti.formal.automation.datatypes.ReferenceType;
import edu.kit.iti.formal.automation.st.Identifiable;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import edu.kit.iti.formal.automation.st.util.Tuple;
import edu.kit.iti.formal.automation.stoo.STOOSimplifier;
import edu.kit.iti.formal.automation.visitors.Visitable;
import javafx.collections.FXCollections;
import javafx.collections.transformation.SortedList;
import lombok.Getter;
import org.apache.commons.collections4.CollectionUtils;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * Create branches in statements so an instance access always returns a predictable (static) type.
 * Depends on instance IDs.
 *
 * @author Augusto Modanese
 */
public class BranchEffectiveTypes extends STOOTransformation {
    @Override
    public void transform(@NotNull STOOSimplifier.State state) {
        super.transform(state);
        state.getTopLevelElements().accept(new BranchEffectiveTypesVisitor());
    }

    /**
     * Visit statements and find a deferred instance reference, if any exists. A deferred instance reference isType one
     * whose effective data type has not been set.
     */
    @Getter
    private static class FindDeferredInstanceReferenceVisitor extends AstVisitor<Object> {
        /**
         * The instance reference, if we find it.
         */
        @Nullable
        private SymbolicReference deferredInstanceReference = null;

        boolean found() {
            return deferredInstanceReference != null;
        }

        void reset() {
            deferredInstanceReference = null;
        }

        @Nullable
        @Override
        public Object defaultVisit(Visitable visitable) {
            if (found())
                return null;
            return super.defaultVisit(visitable);
        }

        @Nullable
        @Override
        public Object visit(@NotNull SymbolicReference symbolicReference) {
            if (found())
                return null;
            List<SymbolicReference> symbolicReferenceList = symbolicReference.asList();
            Optional<SymbolicReference> instanceReferenceOptional = symbolicReferenceList.stream()
                    .filter(sr -> sr.getEffectiveDataType() == null)
                    .filter(sr -> sr.getIdentifiedObject() instanceof VariableDeclaration)
                    .filter(sr -> {
                        AnyDt referencedType = ((VariableDeclaration) sr.getIdentifiedObject()).getDataType();
                        // Only consider references and interface types
                        if (referencedType instanceof InterfaceDataType)
                            return sr.hasSub();
                        if (!(referencedType instanceof ReferenceType))
                            return false;
                        // Accept reference only if it belongs to an actual instance
                        for (int i = 0; i < sr.getDerefCount(); i++)
                            referencedType = ((ReferenceType) referencedType).getOf();
                        return referencedType instanceof ClassDataType;
                    })
                    .map(sr -> new SymbolicReference(symbolicReferenceList.subList(0,
                            symbolicReferenceList.indexOf(sr) + 1)))
                    .findFirst();
            instanceReferenceOptional.ifPresent(sr -> deferredInstanceReference = sr);
            return null;
        }
    }

    /**
     * Visit statements and set the effective type (i.e., identified object) of the given reference to the given object.
     */
    @Getter
    private static class SetEffectiveTypeToReferenceVisitor extends AstVisitor<Object> {
        /**
         * The reference whose effective type we want to set.
         */
        @NotNull
        private final SymbolicReference theReference;

        /**
         * theReference as a list.
         */
        @NotNull
        private final List<SymbolicReference> theReferenceAsList;

        /**
         * The effective type to set.
         */
        @NotNull
        private final AnyDt effectiveType;

        SetEffectiveTypeToReferenceVisitor(@NotNull SymbolicReference theReference, @NotNull AnyDt effectiveType) {
            this.theReference = theReference;
            this.effectiveType = effectiveType;
            theReferenceAsList = theReference.asList();
        }

        /**
         * @param a The first reference.
         * @param b The second reference.
         * @return Whether references a and b match. Ignore sub-references of the longest one in case their sizes are
         * different.
         */
        private boolean referenceMatches(@NotNull List<SymbolicReference> a, @NotNull List<SymbolicReference> b) {
            // Base case
            if (a.size() == 0 || b.size() == 0)
                return true;
            // Compare first item
            // TODO: consider subscripts
            if (!a.get(0).getIdentifier().equals(b.get(0).getIdentifier()))
                return false;
            // Recurse
            return referenceMatches(a.subList(1, a.size()), b.subList(1, b.size()));
        }

        @Nullable
        @Override
        public Object visit(@NotNull SymbolicReference symbolicReference) {
            List<SymbolicReference> symbolicReferenceList = symbolicReference.asList();
            if (referenceMatches(symbolicReferenceList, theReferenceAsList))
                symbolicReferenceList.get(theReferenceAsList.size() - 1).setEffectiveDataType(effectiveType);
            return null;
        }
    }

    private class BranchEffectiveTypesVisitor extends AstMutableVisitor {
        @NotNull Object visit(@NotNull Statement statement) {
            FindDeferredInstanceReferenceVisitor findDeferredInstanceReferenceVisitor
                    = new FindDeferredInstanceReferenceVisitor();
            statement.accept(findDeferredInstanceReferenceVisitor);
            while (findDeferredInstanceReferenceVisitor.found()) {
                assert findDeferredInstanceReferenceVisitor.getDeferredInstanceReference() != null;
                statement = createIfStatement(statement,
                        findDeferredInstanceReferenceVisitor.getDeferredInstanceReference());
                // Perform search once more
                findDeferredInstanceReferenceVisitor.reset();
                statement.accept(findDeferredInstanceReferenceVisitor);
            }
            return statement;
        }

        @NotNull
        @Override
        public Object visit(@NotNull StatementList statements) {
            StatementList statementList = new StatementList();
            for (Statement statement : statements) {
                // We need to handle guarded statements differently since the guard cannot contain another if statement
                if (statement instanceof IfStatement) {
                    IfStatement ifStatement = (IfStatement) statement;
                    IfStatement newIfStatement = new IfStatement();
                    for (GuardedStatement guardedStatement : ifStatement.getConditionalBranches())
                        newIfStatement.addGuardedCommand(guardedStatement.getCondition(),
                                (StatementList) guardedStatement.getStatements().accept(this));
                    newIfStatement.setElseBranch((StatementList) ifStatement.getElseBranch().accept(this));
                    statement = newIfStatement;
                }
                else if (statement instanceof CaseStatement) {
                    CaseStatement caseStatement = (CaseStatement) statement;
                    CaseStatement newCaseStatement = new CaseStatement();
                    newCaseStatement.setExpression(caseStatement.getExpression());
                    for (CaseStatement.Case c : caseStatement.getCases())
                        newCaseStatement.addCase(new CaseStatement.Case(
                                c.getConditions(), (StatementList) c.getStatements().accept(this)
                        ));
                    newCaseStatement.setElseCase((StatementList) caseStatement.getElseCase().accept(this));
                    statement = newCaseStatement;
                }
                else if (statement instanceof GuardedStatement) {
                    GuardedStatement guardedStatement = (GuardedStatement) statement;
                    guardedStatement.setStatements((StatementList) guardedStatement.getStatements().accept(this));
                    // statement = guardedStatement;
                }
                statementList.add((Statement) visit(statement));
            }
            return statementList;
        }

        /**
         * @param originalStatement     The statement to create branches for.
         * @param deferredTypeReference The reference with deferred type we are branching in.
         * @return An if statement with a block for each effective type the reference can have. If the reference has
         * a single effective type, then return the original statement. In both cases, the reference isType assigned the
         * effective type it isType assumed to have inside the block.
         */
        @NotNull
        private Statement createIfStatement(@NotNull Statement originalStatement,
                                            @NotNull SymbolicReference deferredTypeReference) {
            IfStatement branch = new IfStatement();
            // Find variable
            Identifiable parent = getCurrentTopLevelScopeElement();
            SymbolicReference reference = deferredTypeReference;
            while (reference.hasSub() && reference.getDerefCount() == 0) {
                parent = reference.getIdentifiedObject();
                if (parent instanceof VariableDeclaration
                    && ((VariableDeclaration) parent).getDataType() instanceof ClassDataType)
                    parent = ((ClassDataType) ((VariableDeclaration) parent).getDataType()).getClazz();
                reference = reference.getSub();
            }
            assert reference.getIdentifiedObject() instanceof VariableDeclaration;
            assert parent instanceof HasScope;
            // Add branches based on the instance reference we found
            Set<AnyDt> effectiveTypes =
                    state.getEffectiveSubtypeScope().getTypes((VariableDeclaration) reference.getIdentifiedObject());
            // Keep statements intact we case we don't find any reference to an instance
            // or when everything stays the same (see below)
            boolean allBlocksEqual = true;  // true until false
            StatementList lastBlock = null;
            if (effectiveTypes.size() > 1 && !((VariableDeclaration) reference.getIdentifiedObject()).isConstant())
                for (AnyDt effectiveType : new SortedList<>(FXCollections.observableArrayList(effectiveTypes))) {
                    StatementList block = new StatementList(originalStatement.clone());
                    //block.add(0, new CommentStatement(deferredTypeReference + " : " + effectiveType.getName()));
                    SetEffectiveTypeToReferenceVisitor setEffectiveTypeVisitor =
                            new SetEffectiveTypeToReferenceVisitor(deferredTypeReference, effectiveType);
                    block.accept(setEffectiveTypeVisitor);
                    for (Tuple<Integer, Integer> instanceIDRange
                            : state.getInstanceIDRangesToClass((ClassDataType) effectiveType, false)) {
                        Expression guard = instanceIDInRangeGuard(deferredTypeReference, instanceIDRange);
                        guard.accept(setEffectiveTypeVisitor);
                        branch.addGuardedCommand(guard, block);
                        if (allBlocksEqual) {
                            if (lastBlock != null)
                                allBlocksEqual = CollectionUtils.isEqualCollection(block, lastBlock);
                            lastBlock = block;
                        }
                    }
                }
            else {
                assert !((VariableDeclaration) reference.getIdentifiedObject()).isConstant()
                        || effectiveTypes.size() == 1;
                Optional o = effectiveTypes.stream().findAny();
                assert o.isPresent();
                originalStatement.accept(new SetEffectiveTypeToReferenceVisitor(deferredTypeReference, (AnyDt) o.get()));
            }
            // Everything stays the same?
            if (branch.getConditionalBranches().isEmpty())
                return originalStatement;
            if (allBlocksEqual) {
                assert branch.getConditionalBranches().get(0).getStatements().size() == 1;
                return branch.getConditionalBranches().get(0).getStatements().get(0);
            }
            return branch;
        }

        /**
         * @param instanceReference The reference.
         * @param instanceIDRange   The range of IDs the instance should be in.
         * @return A guard which evaluates to true iff the ID of the instance which deferredInstanceReference references isType
         * in the range defined by instanceIDRange.
         */
        private Expression instanceIDInRangeGuard(@NotNull SymbolicReference instanceReference,
                                                  @NotNull Tuple<Integer, Integer> instanceIDRange) {
            SymbolicReference instanceIDReference = instanceReference.clone();
            List<SymbolicReference> instanceIDReferenceList = instanceIDReference.asList();
            instanceIDReferenceList.get(instanceIDReferenceList.size() - 1).setSub(
                    new SymbolicReference(INSTANCE_ID_VAR_NAME));
            // _INSTANCE_ID >= instanceIDRange(lower) AND _INSTANCE_ID <= instanceIDRange(upper)
            AnyDt instanceIDType = state.getGlobalScope().resolveDataType(
                    INSTANCE_ID_VAR_NAME + INSTANCE_ID_TYPE_SUFFIX);
            return BinaryExpression.Companion.andExpression(
                    BinaryExpression.Companion.greaterEqualsExpression(instanceIDReference,
                            new Literal(instanceIDType, Integer.toString(instanceIDRange.getA()))),
                    BinaryExpression.Companion.lessEqualsExpression(instanceIDReference,
                            new Literal(instanceIDType, Integer.toString(instanceIDRange.getB()))));
        }
    }
}
