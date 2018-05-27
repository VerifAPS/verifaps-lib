package edu.kit.iti.formal.automation.oo

import com.google.common.collect.Streams
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.ast.ClassDeclaration
import edu.kit.iti.formal.automation.st.ast.InterfaceDeclaration
import edu.kit.iti.formal.automation.st.ast.MethodDeclaration

import java.util.ArrayList
import java.util.stream.Collectors

/**
 * Misc OO utils. Offloads logic from AST classes.
 *
 * TODO change methods to support both classes and interfaces
 *
 * @author Augusto Modanese
 */
object OOUtils {
    /**
     * @return (a shallow clone of) the class' local scope when accounting for inheritance
     */
    fun getEffectiveScope(clazz: ClassDeclaration): Scope {
        // Base case
        if (!clazz.hasParentClass())
            return clazz.scope.shallowCopy()
        val localScope = clazz.scope.shallowCopy()
        getEffectiveScope(clazz.parentClass!!).asMap().values.stream()
                // Disconsider obfuscated variables
                .filter { v -> !localScope.hasVariable(v.name) }
                .forEach(Consumer<VariableDeclaration> { localScope.add(it) })
        return localScope
    }

    /**
     * To be called only after bound to global scope!
     *
     * @return The list of classes the class can be an instance of, taking polymorphy into account.
     */
    fun getExtendedClasses(clazz: ClassDeclaration): List<ClassDeclaration> {
        val extendedClasses = ArrayList<ClassDeclaration>()
        extendedClasses.add(clazz)
        val parentClass = clazz.parentClass
        if (parentClass != null)
            extendedClasses.addAll(getExtendedClasses(parentClass))
        return extendedClasses
    }

    /**
     * To be called only after bound to global scope!
     *
     * @return Whether the class extends the given other class.
     */
    fun extendsClass(oneClass: ClassDeclaration, otherClass: ClassDeclaration?): Boolean {
        val parentClass = oneClass.parentClass
        if (parentClass === otherClass)
            return true
        else if (parentClass == null)
            return false  // reached top of hierarchy
        return extendsClass(oneClass, oneClass.parentClass)
    }

    /**
     * To be called only after bound to global scope!
     *
     * @return The interfaces the class implements. Includes the interfaces of all parent classes.
     */
    fun getImplementedInterfaces(clazz: ClassDeclaration): List<InterfaceDeclaration> {
        val implementedInterfaces = clazz.interfaces.parallelStream()
                .map<InterfaceDeclaration>(Function<RefTo<InterfaceDeclaration>, InterfaceDeclaration> { it.getIdentifiedObject() }).collect<List<InterfaceDeclaration>, Any>(Collectors.toList())
        // Add interfaces from parent classes
        val parentClass = clazz.parentClass
        if (parentClass != null)
            implementedInterfaces.addAll(getImplementedInterfaces(parentClass))
        // Add extended interfaces
        implementedInterfaces.addAll(implementedInterfaces.parallelStream()
                .map<List<RefTo<InterfaceDeclaration>>>(Function<InterfaceDeclaration, List<RefTo<InterfaceDeclaration>>> { it.getInterfaces() })
                .flatMap { l -> l.parallelStream().map<InterfaceDeclaration>(Function<RefTo<InterfaceDeclaration>, InterfaceDeclaration> { it.getIdentifiedObject() }) }
                .collect<List<InterfaceDeclaration>, Any>(Collectors.toList()))
        return implementedInterfaces
    }

    /**
     * To be called only after bound to global scope!
     *
     * @return Whether the class implements the given interface.
     */
    fun implementsInterface(clazz: ClassDeclaration, interfaze: InterfaceDeclaration): Boolean {
        return getImplementedInterfaces(clazz).contains(interfaze)
    }

    fun getMethod(clazz: ClassDeclaration, identifier: String): MethodDeclaration {
        if (hasMethod(clazz, identifier))
            return clazz.methods.parallelStream()
                    .filter { m -> m.name == identifier }.findAny().get()
        assert(hasMethodWithInheritance(clazz, identifier))
        return getMethodsWithInheritance(clazz).stream()
                .filter { m -> m.name == identifier }
                .findAny().get()
    }

    fun getMethod(interfaze: InterfaceDeclaration, identifier: String): MethodDeclaration {
        if (hasMethod(interfaze, identifier))
            return interfaze.methods.parallelStream()
                    .filter { m -> m.name == identifier }.findAny().get()
        assert(hasMethodWithInheritance(interfaze, identifier))
        return getMethodsWithInheritance(interfaze).stream()
                .filter { m -> m.name == identifier }
                .findAny().get()
    }

    /**
     * @return Whether the class has a method with the given name (not accounting for inheritance).
     * @see .hasMethodWithInheritance
     */
    fun hasMethod(clazz: ClassDeclaration, method: String): Boolean {
        return clazz.methods.parallelStream().anyMatch { m -> m.name == method }
    }

    fun hasMethod(interfaze: InterfaceDeclaration, method: String): Boolean {
        return interfaze.methods.parallelStream().anyMatch { m -> m.name == method }
    }

    /**
     * @return The class' methods, accounting for inheritance (parent classes).
     */
    fun getMethodsWithInheritance(clazz: ClassDeclaration): List<MethodDeclaration> {
        if (!clazz.hasParentClass())
            return clazz.methods
        val parentMethods = getMethodsWithInheritance(clazz.parentClass!!)
        // Make sure to remove obfuscated and overriden methods from parent
        return Streams.concat(parentMethods.stream().filter { m -> !hasMethod(clazz, m.name) },
                clazz.methods.stream())
                .collect<List<MethodDeclaration>, Any>(Collectors.toList())
    }

    /**
     * @return The interface's methods, accounting for inheritance (parent interfaces).
     */
    fun getMethodsWithInheritance(interfaze: InterfaceDeclaration): List<MethodDeclaration> {
        if (interfaze.interfaces.isEmpty())
        // top-level interface
            return interfaze.methods
        val parentMethods = interfaze.interfaces.parallelStream()
                .flatMap { i -> getMethodsWithInheritance(i.obj!!).parallelStream() }
                .collect<List<MethodDeclaration>, Any>(Collectors.toList())
        // Make sure to remove obfuscated and overriden methods from parent
        return Streams.concat(parentMethods.parallelStream()
                .filter { m -> !hasMethod(interfaze, m.name) }, interfaze.methods.parallelStream())
                .collect<List<MethodDeclaration>, Any>(Collectors.toList())
    }

    /**
     * @return Whether the class has a method with the given name, accounting for inheritance (parent classes).
     */
    fun hasMethodWithInheritance(clazz: ClassDeclaration, method: String): Boolean {
        return getMethodsWithInheritance(clazz).parallelStream().anyMatch { m -> m.name == method }
    }

    fun hasMethodWithInheritance(interfaze: InterfaceDeclaration, method: String): Boolean {
        return getMethodsWithInheritance(interfaze).parallelStream().anyMatch { m -> m.name == method }
    }

    /**
     * @return (a shallow clone of) the method's local scope, accounting for its parent's (effective) local scope too
     */
    fun getFullScope(method: MethodDeclaration): Scope {
        val fullScope = method.scope.shallowCopy()
        if (method.parent is ClassDeclaration)
            getEffectiveScope(method.parent as ClassDeclaration).forEach(Consumer<VariableDeclaration> { fullScope.add(it) })
        return fullScope
    }
}
