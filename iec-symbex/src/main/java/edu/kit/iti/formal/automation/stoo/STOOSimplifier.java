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

import com.google.common.collect.ImmutableList;
import edu.kit.iti.formal.automation.datatypes.ClassDataType;
import edu.kit.iti.formal.automation.scope.EffectiveSubtypeScope;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.st.ast.ClassDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.stoo.trans.*;
import javafx.util.Pair;
import lombok.AllArgsConstructor;
import lombok.Data;

import java.util.ArrayList;
import java.util.List;
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

    public STOOSimplifier(TopLevelElement astRoot, TopLevelElements topLevelElements, GlobalScope globalScope,
                          InstanceScope instanceScope, EffectiveSubtypeScope effectiveSubtypeScope) {
        state = new State(astRoot, topLevelElements, globalScope, instanceScope, effectiveSubtypeScope);
    }

    public void simplify() {
        System.out.println("Found " + state.instances.size() + " instances");
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
        private final GlobalScope globalScope;
        private final InstanceScope instanceScope;
        private final EffectiveSubtypeScope effectiveSubtypeScope;
        private final List<InstanceScope.Instance> instances;

        public State(TopLevelElement topLevelElement, TopLevelElements topLevelElements, GlobalScope globalScope,
                     InstanceScope instanceScope, EffectiveSubtypeScope effectiveSubtypeScope) {
            this(topLevelElement, topLevelElements, globalScope, instanceScope, effectiveSubtypeScope,
                    instanceScope.getAllInstances());
        }

        public int getInstanceID(InstanceScope.Instance instance) {
            return instances.indexOf(instance);
        }

        /**
         * @param clazz The class declaration.
         * @param polymorph Whether to include instances of subclasses as well.
         * @return The list of ranges of IDs the instances of clazz are in.
         */
        public List<Pair<Integer, Integer>> getInstanceIDRangesToClass(ClassDeclaration clazz, boolean polymorph) {
            List<Pair<Integer, Integer>> idRanges = new ArrayList<>();
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
                    idRanges.add(new Pair<>(lower, lower + i - instanceIDs.indexOf(lower) - 1));
                    if (i < instanceIDs.size())
                        lower = instanceIDs.get(i);
                }
            return idRanges;
        }

        public List<Pair<Integer, Integer>> getInstanceIDRangesToClass(ClassDataType clazz, boolean polymorph) {
            return getInstanceIDRangesToClass(clazz.getClazz(), polymorph);
        }

        public List<Pair<Integer, Integer>> getInstanceIDRangesToClass(ClassDeclaration clazz) {
            // polymorph = true is the default
            return getInstanceIDRangesToClass(clazz, true);
        }

        public List<Pair<Integer, Integer>> getInstanceIDRangesToClass(ClassDataType clazz) {
            // polymorph = true is the default
            return getInstanceIDRangesToClass(clazz.getClazz(), true);
        }
    }
}
