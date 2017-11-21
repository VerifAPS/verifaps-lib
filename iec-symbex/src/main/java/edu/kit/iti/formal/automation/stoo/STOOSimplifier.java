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
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.st.ast.ClassDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.stoo.trans.BranchEffectiveTypes;
import edu.kit.iti.formal.automation.stoo.trans.GlobalInstances;
import edu.kit.iti.formal.automation.stoo.trans.STOOTransformation;
import javafx.util.Pair;
import lombok.AllArgsConstructor;
import lombok.Data;

import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Augusto Modanese
 */
@Data
public class STOOSimplifier {
    public final static List<STOOTransformation> TRANSFORMATIONS = ImmutableList.of(
            new GlobalInstances(),
            new BranchEffectiveTypes()
            //new ReferenceToArrayAccess(),
            //new MethodToFunction()
    );

    private final State state;

    public void simplify() {
        for (STOOTransformation transformation : TRANSFORMATIONS)
            transformation.transform(state);
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
        private final List<InstanceScope.Instance> instances;

        public State(TopLevelElement topLevelElement, TopLevelElements topLevelElements, GlobalScope globalScope,
                     InstanceScope instanceScope) {
            this(topLevelElement, topLevelElements, globalScope, instanceScope, instanceScope.getAllInstances());
        }

        public int getInstanceID(InstanceScope.Instance instance) {
            return instances.indexOf(instance);
        }

        /**
         * @param clazz The class declaration.
         * @param polymorph Whether to include instances of subclasses as well.
         * @return The range of IDs the instances of clazz are in.
         */
        public Pair<Integer, Integer> getInstanceIDRangeToClass(ClassDeclaration clazz, boolean polymorph) {
            List<InstanceScope.Instance> instances = polymorph
                    ? instanceScope.getPolymorphInstancesOfClass(clazz)
                    : instanceScope.getInstancesOfClass(clazz);
            List<Integer> instanceIDs = instances.stream().map(this::getInstanceID).collect(Collectors.toList());
            return new Pair<>(instanceIDs.stream().min(Comparator.naturalOrder()).get(),
                    instanceIDs.stream().max(Comparator.naturalOrder()).get());
        }

        public Pair<Integer, Integer> getInstanceIDRangeToClass(ClassDataType clazz, boolean polymorph) {
            return getInstanceIDRangeToClass(clazz.getClazz(), polymorph);
        }

        public Pair<Integer, Integer> getInstanceIDRangeToClass(ClassDeclaration clazz) {
            // polymorph = true is the default
            return getInstanceIDRangeToClass(clazz, true);
        }

        public Pair<Integer, Integer> getInstanceIDRangeToClass(ClassDataType clazz) {
            // polymorph = true is the default
            return getInstanceIDRangeToClass(clazz.getClazz(), true);
        }
    }
}
