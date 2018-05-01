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

package edu.kit.iti.formal.automation.stoo;

import edu.kit.iti.formal.automation.scope.EffectiveSubtypeScope;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.automation.st.util.Tuple;
import com.google.common.collect.ImmutableList;
import edu.kit.iti.formal.automation.datatypes.ClassDataType;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.st.ast.ClassDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.stoo.trans.*;
import lombok.AllArgsConstructor;
import lombok.Data;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * @author Augusto Modanese
 */
@Data
@AllArgsConstructor
public class STOOSimplifier {
    public static final List<Class<? extends STOOTransformation>> TRANSFORMATIONS = ImmutableList.of(
            GlobalInstances.class,
            BranchEffectiveTypes.class,
            Inheritance.class,
            MethodToFunction.class,
            ReferenceToArrayAccess.class,
            ClassToRecord.class
    );

    private final State state;

    public STOOSimplifier(TopLevelElement astRoot, TopLevelElements topLevelElements, Scope globalScope,
                          InstanceScope instanceScope, EffectiveSubtypeScope effectiveSubtypeScope) {
        state = new State(astRoot, topLevelElements, globalScope, instanceScope, effectiveSubtypeScope);
    }

    public void simplify() {
        for (Class<? extends STOOTransformation> transformation : TRANSFORMATIONS)
            try {
                transformation.newInstance().transform(state);
            } catch (InstantiationException | IllegalAccessException e) {
                e.printStackTrace();
            }
    }

    @Data
    @AllArgsConstructor
    public static class State {
        /**
         * The root of the AST subtree to visit. Usually the program to verify.
         */
        private final TopLevelElement topLevelElement;

        private final TopLevelElements topLevelElements;

        private final Scope globalScope;
        private final InstanceScope instanceScope;
        private final EffectiveSubtypeScope effectiveSubtypeScope;
        private final List<InstanceScope.Instance> instances;

        public State(TopLevelElement topLevelElement, TopLevelElements topLevelElements, Scope globalScope,
                     InstanceScope instanceScope, EffectiveSubtypeScope effectiveSubtypeScope) {
            this(topLevelElement, topLevelElements, globalScope, instanceScope, effectiveSubtypeScope,
                    instanceScope.getAllInstances());
        }

        public int getInstanceID(InstanceScope.Instance instance) {
            return instances.indexOf(instance);
        }

        public Scope getGlobalScope() {
            return globalScope;
        }

        /**
         * @deprecated use {@link #getGlobalScope()} instead
         */
        @Deprecated
        public Scope getScope() {
            return getGlobalScope();
        }

        /**
         * @param clazz The class declaration.
         * @param polymorph Whether to include instances of subclasses as well.
         * @return The list of ranges of IDs the instances of clazz are in.
         */
        public List<Tuple<Integer, Integer>> getInstanceIDRangesToClass(ClassDeclaration clazz, boolean polymorph) {
            List<Tuple<Integer, Integer>> idRanges = new ArrayList<>();
            List<InstanceScope.Instance> instances = polymorph
                    ? instanceScope.getPolymorphInstancesOfClass(clazz)
                    : instanceScope.getInstancesOfClass(clazz);
            List<Integer> instanceIDs = instances.stream().map(this::getInstanceID).collect(Collectors.toList());
            assert instanceIDs.size() > 0;
            instanceIDs.sort(Integer::compareTo);
            // Create ranges
            int lower = instanceIDs.get(0);
            for (int i = 0; i <= instanceIDs.size(); i++)
                if (i == instanceIDs.size() || instanceIDs.get(i) - lower > i) {
                    idRanges.add(new Tuple<>(lower, lower + i - instanceIDs.indexOf(lower) - 1));
                    if (i < instanceIDs.size())
                        lower = instanceIDs.get(i);
                }
            return idRanges;
        }

        public List<Tuple<Integer, Integer>> getInstanceIDRangesToClass(ClassDataType clazz, boolean polymorph) {
            return getInstanceIDRangesToClass(clazz.getClazz(), polymorph);
        }

        public List<Tuple<Integer, Integer>> getInstanceIDRangesToClass(ClassDeclaration clazz) {
            // polymorph = true is the default
            return getInstanceIDRangesToClass(clazz, true);
        }

        public List<Tuple<Integer, Integer>> getInstanceIDRangesToClass(ClassDataType clazz) {
            // polymorph = true is the default
            return getInstanceIDRangesToClass(clazz.getClazz(), true);
        }

        public Set<InstanceScope.Instance> getInstancesOfVariable(VariableDeclaration variable) {
            return instanceScope.getInstances(variable);
        }
    }
}
