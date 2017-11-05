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

import edu.kit.iti.formal.automation.st.ast.*;
import lombok.Data;
import lombok.ToString;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Scope representing class and FB instances in the program being analyzed.
 *
 * @author Augusto Modanese
 */
@ToString
public class InstanceScope implements Serializable {
    private final GlobalScope globalScope;
    private Map<ClassDeclaration, List<Instance>> classInstances = new HashMap();
    private Map<FunctionBlockDeclaration, List<Instance>> functionBlockInstances = new HashMap();
    private Map<InterfaceDeclaration, List<Instance>> interfaceInstances = new HashMap();
    private Map<ClassDeclaration, List<Instance>> classPolymorphInstances = new HashMap();
    private Map<FunctionBlockDeclaration, List<Instance>> functionBlockPolymorphInstances = new HashMap();

    public InstanceScope(GlobalScope globalScope) {
        this.globalScope = globalScope;
        for (InterfaceDeclaration interfaceDeclaration : globalScope.getInterfaces())
            interfaceInstances.put(interfaceDeclaration, new ArrayList());
        for (ClassDeclaration classDeclaration : globalScope.getClasses()) {
            classInstances.put(classDeclaration, new ArrayList());
            classPolymorphInstances.put(classDeclaration, new ArrayList());
        }
        for (FunctionBlockDeclaration functionBlockDeclaration : globalScope.getFunctionBlocks()) {
            functionBlockInstances.put(functionBlockDeclaration, new ArrayList());
            functionBlockPolymorphInstances.put(functionBlockDeclaration, new ArrayList());
        }
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
        return functionBlockInstances.get(functionBlockDeclaration);
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
        return functionBlockPolymorphInstances.get(functionBlockDeclaration);
    }

    public void registerClassInstance(ClassDeclaration classDeclaration, Instance instance) {
        classInstances.get(classDeclaration).add(instance);
        classDeclaration.getImplementedInterfaces().forEach(i -> interfaceInstances.get(i).add(instance));
        classDeclaration.getExtendedClasses().forEach(c -> classPolymorphInstances.get(c).add(instance));
    }

    public void registerFunctionBlockInstance(FunctionBlockDeclaration functionBlockDeclaration,
                                              Instance instance) {
        functionBlockInstances.get(functionBlockDeclaration).add(instance);
        functionBlockDeclaration.getImplementedInterfaces().forEach(i -> interfaceInstances.get(i).add(instance));
        functionBlockDeclaration.getExtendedClasses().forEach(c -> {
            if (c instanceof FunctionBlockDeclaration)
                functionBlockPolymorphInstances.get(c).add(instance);
            else
                // Function blocks may also extend classes
                classPolymorphInstances.get(c).add(instance);
        });
    }

    /**
     * Model an instance of a class or function block. Maintains a reference to where the instance is declared.
     */
    @Data
    public static class Instance {
        /**
         * Null iff parent is a program.
         */
        private final Instance parent;

        private final VariableDeclaration variableDeclaration;
    }
}
