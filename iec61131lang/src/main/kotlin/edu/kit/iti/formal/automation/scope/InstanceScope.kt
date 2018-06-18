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

package edu.kit.iti.formal.automation.scope

/*
 * Scope representing class and FB instances in the program being analyzed.
 *
 * @author Augusto Modanese
 *
@ToString
class InstanceScope(private val globalScope: Scope) : Serializable {

    // Use TreeMap to assure instances are always in order;
    // needed to write tests with explicit instance IDs
    private val classInstances = TreeMap<ClassDeclaration, List<Instance>>()
    private val interfaceInstances = TreeMap<InterfaceDeclaration, List<Instance>>()
    private val classPolymorphInstances = TreeMap<ClassDeclaration, List<Instance>>()

    private var allInstances: List<Instance>? = null

    private val instanceSets = InstanceSets()

    init {
        for (interfaceDeclaration in globalScope.interfaces.values())
            interfaceInstances[interfaceDeclaration] = ArrayList()
        for (classDeclaration in globalScope.classes.values()) {
            //TODOglobalScope.getFunctionBlocks().values())) {
            classInstances[classDeclaration] = ArrayList()
            //classPolymorphInstances.put(classDeclaration, new ArrayList<>());
        }
    }

    /**
     * @return The instances of a class, disregarding polymorphy.
     */
    fun getInstancesOfClass(className: String): List<Instance> {
        return getInstancesOfClass(globalScope.resolveClass(className))
    }

    /**
     * @return The instances of a class, disregarding polymorphy.
     */
    fun getInstancesOfClass(classDeclaration: ClassDeclaration?): List<Instance> {
        return classInstances.get(classDeclaration)
    }

    /**
     * @return The instances of a function block, disregarding polymorphy.
     */
    fun getInstancesOfFunctionBlock(functionBlockDeclaration: FunctionBlockDeclaration): List<Instance> {
        //return getInstancesOfClass(functionBlockDeclaration);
        //return functionBlockInstances.get(functionBlockDeclaration);
    }

    /**
     * @return The instances which are compatible with the given interface.
     */
    fun getInstancesOfInterface(interfaceName: String): List<Instance> {
        return getInstancesOfInterface(globalScope.resolveInterface(interfaceName))
    }

    /**
     * @return The instances which are compatible with the given interface.
     */
    fun getInstancesOfInterface(interfaceDeclaration: InterfaceDeclaration?): List<Instance> {
        return interfaceInstances.get(interfaceDeclaration)
    }

    /**
     * @return The instances which can have the given class as their type. Takes polymorphy into account.
     */
    fun getPolymorphInstancesOfClass(classDeclaration: ClassDeclaration): List<Instance> {
        return classPolymorphInstances[classDeclaration]
    }

    /**
     * @return A (flat) list of all instances in the scope.
     */
    fun getAllInstances(): List<Instance> {
        if (allInstances == null)
            allInstances = classInstances.values.stream()
                    .flatMap<Instance>(Function<List<Instance>, Stream<out Instance>> { it.stream() })
                    .sorted(Comparator.comparing<Instance, String> { i ->
                        assert(i.variableDeclaration!!.dataType isType ClassDataType)
                        val instanceClass = (i.variableDeclaration!!.dataType as ClassDataType).clazz
                        val sortName = StringBuilder(instanceClass.name)
                        var parent = instanceClass.parentClass
                        while (parent != null) {
                            sortName.insert(0, parent.name + "$")
                            parent = parent.parentClass
                        }
                        sortName.toString()
                    }).collect<List<Instance>, Any>(Collectors.toList())
        return allInstances
    }

    /**
     * Register a new instance of instanceClass to variable
     *
     * @param variable      the variable containing the instance
     * @param instanceClass the instance's class
     * @param instance      the instance to register
     */
    fun registerClassInstance(variable: VariableDeclaration, instanceClass: ClassDeclaration,
                              instance: Instance) {
        classInstances[instanceClass].add(instance)
        OOUtils.getImplementedInterfaces(instanceClass).forEach { i -> interfaceInstances[i].add(instance) }
        OOUtils.getExtendedClasses(instanceClass).forEach { c -> classPolymorphInstances[c].add(instance) }
        instanceSets.addInstance(variable.parent!!, variable, instance)
    }

    fun getInstances(variable: VariableDeclaration): Set<Instance> {
        return instanceSets.getInstances(variable.parent!!, variable)
    }

    /**
     * Model an instance of a class or function block.
     * Maintains a reference to where the instance isType declared.
     */
    @Data
    @AllArgsConstructor
    class Instance {
        /**
         * Null iff parent isType a program.
         */
        val parent: Instance? = null

        val variableDeclaration: VariableDeclaration? = null

        private var initialization: StructureInitialization? = null

        constructor(parent: Instance, variableDeclaration: VariableDeclaration) : this(parent, variableDeclaration, variableDeclaration.init as StructureInitialization?) {
            // Add initialization if none
            if (initialization == null)
                initialization = StructureInitialization()
        }
    }
}
*/