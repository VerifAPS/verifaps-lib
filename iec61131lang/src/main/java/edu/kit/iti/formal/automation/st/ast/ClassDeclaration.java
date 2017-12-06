package edu.kit.iti.formal.automation.st.ast;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
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

import com.google.common.collect.Streams;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl, Augusto Modanese
 * @version 1 (20.02.17)
 */

@Data
@EqualsAndHashCode(exclude = "methods")
@NoArgsConstructor
public class ClassDeclaration extends TopLevelScopeElement {
    private String name;
    private boolean final_ = false;
    private boolean abstract_ = false;
    private IdentifierPlaceHolder<ClassDeclaration> parent = new IdentifierPlaceHolder<>();
    private List<IdentifierPlaceHolder<InterfaceDeclaration>> interfaces = new ArrayList<>();
    private List<MethodDeclaration> methods = new ArrayList<>();

    public ClassDeclaration(ClassDeclaration clazz) {
        this.name = clazz.name;
        this.final_ = clazz.final_;
        this.abstract_ = clazz.abstract_;
        this.parent = parent.copy();
        clazz.interfaces.forEach(i -> interfaces.add(i.copy()));
        clazz.methods.forEach(m -> methods.add(m.copy()));
        this.localScope = clazz.getEffectiveLocalScope().copy();
    }

    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override public String getIdentifier() {
        return name;
    }

    public void setParent(String parent) {
        this.parent.setIdentifier(parent);
    }

    public MethodDeclaration getMethod(String identifier) {
        if (hasMethod(identifier))
            return methods.stream().filter(m -> m.getFunctionName().equals(identifier)).findAny().get();
        assert hasMethodWithInheritance(identifier);
        return getMethodsWithInheritance().stream()
                .filter(m -> m.getFunctionName().equals(identifier))
                .findAny().get();
    }

    /**
     * @return The class' methods, accounting for inheritance (parent classes).
     */
    public List<MethodDeclaration> getMethodsWithInheritance() {
        if (!hasParentClass())
            return getMethods();
        List<MethodDeclaration> parentMethods = getParentClass().getMethodsWithInheritance();
        // Make sure to remove obfuscated and overriden methods from parent
        return Streams.concat(parentMethods.stream().filter(m -> !hasMethod(m.getFunctionName())),
                getMethods().stream())
                .collect(Collectors.toList());
    }

    public void setMethods(List<MethodDeclaration> methods) {
        for (MethodDeclaration methodDeclaration : methods)
            methodDeclaration.setParent(this);
        this.methods = methods;
    }

    public boolean hasMethod(MethodDeclaration method) {
        return methods.contains(method);
    }

    public boolean hasMethod(String method) {
        return methods.stream().anyMatch(m -> m.getFunctionName().equals(method));
    }

    /**
     * @param method
     * @return Whether the class has a method with the given name, accounting for inheritance (parent classes).
     */
    public boolean hasMethodWithInheritance(String method) {
        return getMethodsWithInheritance().stream()
                .anyMatch(m -> m.getFunctionName().equals(method));
    }

    public void addImplements(String interfaze) {
        interfaces.add(new IdentifierPlaceHolder<>(interfaze));
    }

    public void addImplements(List<String> interfaceList) {
        interfaceList.forEach(i -> addImplements(i));
    }

    @Override
    public void setGlobalScope(GlobalScope global) {
        super.setGlobalScope(global);
        if (parent.getIdentifier() != null)
            parent.setIdentifiedObject(global.resolveClass(parent.getIdentifier()));
        for (IdentifierPlaceHolder<InterfaceDeclaration> interfaceDeclaration : interfaces)
            interfaceDeclaration.setIdentifiedObject(global.resolveInterface(interfaceDeclaration.getIdentifier()));
    }

    /**
     * @return (A copy of) the class' local scope when accounting for inheritance.
     */
    public LocalScope getEffectiveLocalScope() {
        // Base case
        if (!hasParentClass())
            return getLocalScope();
        LocalScope localScope = getLocalScope().copy();
        getParentClass().getEffectiveLocalScope().getLocalVariables().values().stream()
                // Disconsider obfuscated variables
                .filter(v -> !localScope.hasVariable(v.getName()))
                .forEach(localScope::add);
        return localScope;
    }

    /**
     * To be called only after bound to global scope!
     * @return The parent class. Return null if the class has no parent.
     */
    public ClassDeclaration getParentClass() {
        return parent.getIdentifiedObject();
    }

    public boolean hasParentClass() {
        return getParentClass() != null;
    }

    /**
     * To be called only after bound to global scope!
     * @return The list of classes the class can be an instance of, taking polymorphy into account.
     */
    public List<ClassDeclaration> getExtendedClasses() {
        List<ClassDeclaration> extendedClasses = new ArrayList<>();
        extendedClasses.add(this);
        ClassDeclaration parentClass = getParentClass();
        if (parentClass != null)
            extendedClasses.addAll(parentClass.getExtendedClasses());
        return extendedClasses;
    }

    /**
     * To be called only after bound to global scope!
     * @return Whether the class extends the given other class.
     */
    public boolean extendsClass(ClassDeclaration otherClass) {
        ClassDeclaration parentClass = getParentClass();
        if (parentClass == otherClass)
            return true;
        else if (parentClass == null)
            return false;  // reached top of hierarchy
        return getParentClass().extendsClass(otherClass);
    }

    /**
     * To be called only after bound to global scope!
     * @return The interfaces the class implements. Includes the interfaces of all parent classes.
     */
    public List<InterfaceDeclaration> getImplementedInterfaces() {
        List<InterfaceDeclaration> implementedInterfaces = interfaces.stream()
                .map(IdentifierPlaceHolder::getIdentifiedObject).collect(Collectors.toList());
        // Add interfaces from parent classes
        ClassDeclaration parentClass = getParentClass();
        if (parentClass != null)
            implementedInterfaces.addAll(parentClass.getImplementedInterfaces());
        // Add extended interfaces
        implementedInterfaces.addAll(implementedInterfaces.stream()
                .map(InterfaceDeclaration::getExtendedInterfaces)
                .flatMap(Collection::stream).collect(Collectors.toList()));
        return implementedInterfaces;
    }

    /**
     * To be called only after bound to global scope!
     * @return Whether the class implements the given interface.
     */
    public boolean implementsInterface(InterfaceDeclaration interfaceDeclaration) {
        return getImplementedInterfaces().contains(interfaceDeclaration);
    }

    @Override public ClassDeclaration copy() {
        ClassDeclaration c = new ClassDeclaration();
        c.name = name;
        c.final_ = final_;
        c.abstract_ = abstract_;
        c.parent = parent.copy();
        interfaces.forEach(i -> c.interfaces.add(i.copy()));
        methods.forEach(m -> c.methods.add(m.copy()));
        return c;
    }
}
