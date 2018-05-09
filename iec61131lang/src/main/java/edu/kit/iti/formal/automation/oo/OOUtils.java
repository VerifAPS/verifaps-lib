package edu.kit.iti.formal.automation.oo;

import com.google.common.collect.Streams;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.st.ast.ClassDeclaration;
import edu.kit.iti.formal.automation.st.ast.Classifier;
import edu.kit.iti.formal.automation.st.ast.InterfaceDeclaration;
import edu.kit.iti.formal.automation.st.ast.MethodDeclaration;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Misc OO utils. Offloads logic from AST classes.
 *
 * TODO change methods to support both classes and interfaces
 *
 * @author Augusto Modanese
 */
public final class OOUtils {
    /**
     * @return (a shallow copy of) the class' local scope when accounting for inheritance
     */
    public static Scope getEffectiveScope(ClassDeclaration clazz) {
        // Base case
        if (!clazz.hasParentClass())
            return clazz.getScope().shallowCopy();
        Scope localScope = clazz.getScope().shallowCopy();
        getEffectiveScope(clazz.getParentClass()).asMap().values().stream()
                // Disconsider obfuscated variables
                .filter(v -> !localScope.hasVariable(v.getName()))
                .forEach(localScope::add);
        return localScope;
    }

    /**
     * To be called only after bound to global scope!
     *
     * @return The list of classes the class can be an instance of, taking polymorphy into account.
     */
    public static List<ClassDeclaration> getExtendedClasses(ClassDeclaration clazz) {
        List<ClassDeclaration> extendedClasses = new ArrayList<>();
        extendedClasses.add(clazz);
        ClassDeclaration parentClass = clazz.getParentClass();
        if (parentClass != null)
            extendedClasses.addAll(getExtendedClasses(parentClass));
        return extendedClasses;
    }

    /**
     * To be called only after bound to global scope!
     *
     * @return Whether the class extends the given other class.
     */
    public static boolean extendsClass(ClassDeclaration oneClass, ClassDeclaration otherClass) {
        ClassDeclaration parentClass = oneClass.getParentClass();
        if (parentClass == otherClass)
            return true;
        else if (parentClass == null)
            return false;  // reached top of hierarchy
        return extendsClass(oneClass, oneClass.getParentClass());
    }

    /**
     * To be called only after bound to global scope!
     *
     * @return The interfaces the class implements. Includes the interfaces of all parent classes.
     */
    public static List<InterfaceDeclaration> getImplementedInterfaces(ClassDeclaration clazz) {
        List<InterfaceDeclaration> implementedInterfaces = clazz.getInterfaces().parallelStream()
                .map(IdentifierPlaceHolder::getIdentifiedObject).collect(Collectors.toList());
        // Add interfaces from parent classes
        ClassDeclaration parentClass = clazz.getParentClass();
        if (parentClass != null)
            implementedInterfaces.addAll(getImplementedInterfaces(parentClass));
        // Add extended interfaces
        implementedInterfaces.addAll(implementedInterfaces.parallelStream()
                .map(InterfaceDeclaration::getInterfaces)
                .flatMap(l -> l.parallelStream().map(IdentifierPlaceHolder::getIdentifiedObject))
                .collect(Collectors.toList()));
        return implementedInterfaces;
    }

    /**
     * To be called only after bound to global scope!
     *
     * @return Whether the class implements the given interface.
     */
    public static boolean implementsInterface(ClassDeclaration clazz, InterfaceDeclaration interfaze) {
        return getImplementedInterfaces(clazz).contains(interfaze);
    }

    public static MethodDeclaration getMethod(ClassDeclaration clazz, String identifier) {
        if (hasMethod(clazz, identifier))
            return clazz.getMethods().parallelStream()
                    .filter(m -> m.getName().equals(identifier)).findAny().get();
        assert hasMethodWithInheritance(clazz, identifier);
        return getMethodsWithInheritance(clazz).stream()
                .filter(m -> m.getName().equals(identifier))
                .findAny().get();
    }

    public static MethodDeclaration getMethod(InterfaceDeclaration interfaze, String identifier) {
        if (hasMethod(interfaze, identifier))
            return interfaze.getMethods().parallelStream()
                    .filter(m -> m.getName().equals(identifier)).findAny().get();
        assert hasMethodWithInheritance(interfaze, identifier);
        return getMethodsWithInheritance(interfaze).stream()
                .filter(m -> m.getName().equals(identifier))
                .findAny().get();
    }

    /**
     * @return Whether the class has a method with the given name (not accounting for inheritance).
     * @see #hasMethodWithInheritance(ClassDeclaration, String)
     */
    public static boolean hasMethod(ClassDeclaration clazz, String method) {
        return clazz.getMethods().parallelStream().anyMatch(m -> m.getName().equals(method));
    }

    public static boolean hasMethod(InterfaceDeclaration interfaze, String method) {
        return interfaze.getMethods().parallelStream().anyMatch(m -> m.getName().equals(method));
    }

    /**
     * @return The class' methods, accounting for inheritance (parent classes).
     */
    public static List<MethodDeclaration> getMethodsWithInheritance(ClassDeclaration clazz) {
        if (!clazz.hasParentClass())
            return clazz.getMethods();
        List<MethodDeclaration> parentMethods = getMethodsWithInheritance(clazz.getParentClass());
        // Make sure to remove obfuscated and overriden methods from parent
        return Streams.concat(parentMethods.stream().filter(m -> !hasMethod(clazz, m.getName())),
                clazz.getMethods().stream())
                .collect(Collectors.toList());
    }

    /**
     * @return The interface's methods, accounting for inheritance (parent interfaces).
     */
    public static List<MethodDeclaration> getMethodsWithInheritance(InterfaceDeclaration interfaze) {
        if (interfaze.getInterfaces().isEmpty())  // top-level interface
            return interfaze.getMethods();
        List<MethodDeclaration> parentMethods = interfaze.getInterfaces().parallelStream()
                .flatMap(i -> getMethodsWithInheritance(i.getIdentifiedObject()).parallelStream())
                .collect(Collectors.toList());
        // Make sure to remove obfuscated and overriden methods from parent
        return Streams.concat(parentMethods.parallelStream()
                        .filter(m -> !hasMethod(interfaze, m.getName())), interfaze.getMethods().parallelStream())
                .collect(Collectors.toList());
    }

    /**
     * @return Whether the class has a method with the given name, accounting for inheritance (parent classes).
     */
    public static boolean hasMethodWithInheritance(ClassDeclaration clazz, String method) {
        return getMethodsWithInheritance(clazz).parallelStream().anyMatch(m -> m.getName().equals(method));
    }

    public static boolean hasMethodWithInheritance(InterfaceDeclaration interfaze, String method) {
        return getMethodsWithInheritance(interfaze).parallelStream().anyMatch(m -> m.getName().equals(method));
    }

    /**
     * @return (a shallow copy of) the method's local scope, accounting for its parent's (effective) local scope too
     */
    public static Scope getFullScope(MethodDeclaration method) {
        Scope fullScope = method.getScope().shallowCopy();
        if (method.getParent() instanceof ClassDeclaration)
            getEffectiveScope((ClassDeclaration) method.getParent()).forEach(fullScope::add);
        return fullScope;
    }
}
