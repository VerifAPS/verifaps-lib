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

package edu.kit.iti.formal.automation.scope;

import edu.kit.iti.formal.automation.analysis.InstanceSets;
import edu.kit.iti.formal.automation.datatypes.ClassDataType;
import edu.kit.iti.formal.automation.st.ast.*;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.ToString;

import java.io.Serializable;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Scope representing class and FB instances in the program being analyzed.
 *
 * @author Augusto Modanese
 */
@ToString
public class InstanceScope implements Serializable {
    private final GlobalScope globalScope;
    // Use TreeMap to assure instances are always in order; needed to write tests with explicit instance IDs
    private Map<ClassDeclaration, List<Instance>> classInstances = new TreeMap();
    //private Map<FunctionBlockDeclaration, List<Instance>> functionBlockInstances = new TreeMap();
    private Map<InterfaceDeclaration, List<Instance>> interfaceInstances = new TreeMap();
    private Map<ClassDeclaration, List<Instance>> classPolymorphInstances = new TreeMap();
    //private Map<FunctionBlockDeclaration, List<Instance>> functionBlockPolymorphInstances = new TreeMap();

    private List<Instance> allInstances;

    private InstanceSets instanceSets = new InstanceSets();

    public InstanceScope(GlobalScope globalScope) {
        this.globalScope = globalScope;
        for (InterfaceDeclaration interfaceDeclaration : globalScope.getInterfaces())
            interfaceInstances.put(interfaceDeclaration, new ArrayList());
        for (ClassDeclaration classDeclaration : globalScope.getClasses()) {
            classInstances.put(classDeclaration, new ArrayList());
            classPolymorphInstances.put(classDeclaration, new ArrayList());
        }
        /*for (FunctionBlockDeclaration functionBlockDeclaration : globalScope.getFunctionBlocks()) {
            functionBlockInstances.put(functionBlockDeclaration, new ArrayList());
            functionBlockPolymorphInstances.put(functionBlockDeclaration, new ArrayList());
        }*/
    }

    /**
     * @return The instances of a class, disregarding polymorphy.
     */
    public List<Instance> getInstancesOfClass(String className) {
        return getInstancesOfClass(globalScope.resolveClass(className));
    }

    /**
     * @return The instances of a class, disregarding polymorphy.
     */
    public List<Instance> getInstancesOfClass(ClassDeclaration classDeclaration) {
        return classInstances.get(classDeclaration);
    }

    /**
     * @return The instances of a function block, disregarding polymorphy.
     */
    public List<Instance> getInstancesOfFunctionBlock(String functionBlockName) {
        return getInstancesOfFunctionBlock(globalScope.getFunctionBlock(functionBlockName));
    }

    /**
     * @return The instances of a function block, disregarding polymorphy.
     */
    public List<Instance> getInstancesOfFunctionBlock(FunctionBlockDeclaration functionBlockDeclaration) {
        return getInstancesOfClass(functionBlockDeclaration);
        //return functionBlockInstances.get(functionBlockDeclaration);
    }

    /**
     * @return The instances which are compatible with the given interface.
     */
    public List<Instance> getInstancesOfInterface(String interfaceName) {
        return getInstancesOfInterface(globalScope.resolveInterface(interfaceName));
    }

    /**
     * @return The instances which are compatible with the given interface.
     */
    public List<Instance> getInstancesOfInterface(InterfaceDeclaration interfaceDeclaration) {
        return interfaceInstances.get(interfaceDeclaration);
    }

    /**
     * @return The instances which can have the given class as their type. Takes polymorphy into account.
     */
    public List<Instance> getPolymorphInstancesOfClass(ClassDeclaration classDeclaration) {
        return classPolymorphInstances.get(classDeclaration);
    }

    /**
     * @return The instances which can have the given function block as their type. Takes polymorphy into account.
     */
    public List<Instance> getPolymorphInstancesOfFunctionBlock(
            FunctionBlockDeclaration functionBlockDeclaration) {
        return getPolymorphInstancesOfClass(functionBlockDeclaration);
        //return functionBlockPolymorphInstances.get(functionBlockDeclaration);
    }

    /**
     * @return A (flat) list of all instances in the scope.
     */
    public List<Instance> getAllInstances() {
        if (allInstances == null)
            allInstances = classInstances.values().stream()
                    .flatMap(Collection::stream)
                    .sorted(Comparator.comparing(i -> {
                        assert i.getVariableDeclaration().getDataType() instanceof ClassDataType;
                        ClassDeclaration instanceClass =
                                ((ClassDataType) i.getVariableDeclaration().getDataType()).getClazz();
                        StringBuilder sortName = new StringBuilder(instanceClass.getName());
                        for (ClassDeclaration parent = instanceClass.getParentClass(); parent != null;
                             parent = parent.getParentClass())
                            sortName.insert(0, parent.getName() + "$");
                        return sortName.toString();
                    })).collect(Collectors.toList());
        return allInstances;
    }

    /**
     * Register a new instance of instanceClass to variable
     * @param variable the variable containing the instance
     * @param instanceClass the instance's class
     * @param instance the instance to register
     */
    public void registerClassInstance(VariableDeclaration variable, ClassDeclaration instanceClass,
                                      Instance instance) {
        classInstances.get(instanceClass).add(instance);
        instanceClass.getImplementedInterfaces().forEach(i -> interfaceInstances.get(i).add(instance));
        instanceClass.getExtendedClasses().forEach(c -> classPolymorphInstances.get(c).add(instance));
        instanceSets.addInstance(variable.getParent(), variable, instance);
    }

    public Set<Instance> getInstances(VariableDeclaration variable) {
        return instanceSets.getInstances(variable.getParent(), variable);
    }

    /**
     * Model an instance of a class or function block. Maintains a reference to where the instance is declared.
     */
    @Data
    @AllArgsConstructor
    public static class Instance {
        /**
         * Null iff parent is a program.
         */
        private final Instance parent;

        private final VariableDeclaration variableDeclaration;

        private StructureInitialization initialization;

        public Instance(Instance parent, VariableDeclaration variableDeclaration) {
            this(parent, variableDeclaration, (StructureInitialization) variableDeclaration.getInit());
            // Add initialization if none
            if (initialization == null)
                initialization = new StructureInitialization();
        }
    }
}
