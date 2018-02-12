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
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.NoArgsConstructor;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

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
public class ClassDeclaration extends Classifier<ParserRuleContext> {
    @NotNull
    private IdentifierPlaceHolder<ClassDeclaration> parent = new IdentifierPlaceHolder<>();
    @NotNull
    private List<MethodDeclaration> methods = new ArrayList<>();
    private boolean final_ = false;
    private boolean abstract_ = false;

    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String getIdentifier() {
        return name;
    }

    public void setParent(String parent) {
        this.parent.setIdentifier(parent);
    }

    public MethodDeclaration getMethod(String identifier) {
        if (hasMethod(identifier))
            return methods.stream().filter(m -> m.getName().equals(identifier)).findAny().get();
        assert hasMethodWithInheritance(identifier);
        return getMethodsWithInheritance().stream()
                .filter(m -> m.getName().equals(identifier))
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
        return Streams.concat(parentMethods.stream().filter(m -> !hasMethod(m.getName())),
                getMethods().stream())
                .collect(Collectors.toList());
    }

    public void setMethods(List<MethodDeclaration> methods) {
        for (MethodDeclaration methodDeclaration : methods) {
            methodDeclaration.setParent(this);
            methodDeclaration.getScope().setParent(scope);
        }
        this.methods = methods;
    }

    public boolean hasMethod(MethodDeclaration method) {
        return methods.contains(method);
    }

    public boolean hasMethod(String method) {
        return methods.stream().anyMatch(m -> m.getName().equals(method));
    }

    /**
     * @param method
     * @return Whether the class has a method with the given name, accounting for inheritance (parent classes).
     */
    public boolean hasMethodWithInheritance(String method) {
        return getMethodsWithInheritance().stream()
                .anyMatch(m -> m.getName().equals(method));
    }

    public void addImplements(String interfaze) {
        interfaces.add(new IdentifierPlaceHolder<>(interfaze));
    }

    public void addImplements(List<String> interfaceList) {
        interfaceList.forEach(i -> addImplements(i));
    }

    /**
     * @return (A copy of) the class' local scope when accounting for inheritance.
     */
    public Scope getEffectiveScope() {
        // Base case
        if (!hasParentClass())
            return getScope();
        Scope localScope = getScope().copy();
        getParentClass().getEffectiveScope().asMap().values().stream()
                // Disconsider obfuscated variables
                .filter(v -> !localScope.hasVariable(v.getName()))
                .forEach(localScope::add);
        return localScope;
    }

    /**
     * To be called only after bound to global scope!
     *
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
     *
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
     *
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
     *
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
     *
     * @return Whether the class implements the given interface.
     */
    public boolean implementsInterface(InterfaceDeclaration interfaceDeclaration) {
        return getImplementedInterfaces().contains(interfaceDeclaration);
    }

    @Override
    public ClassDeclaration copy() {
        ClassDeclaration c = new ClassDeclaration();
        c.name = name;
        c.final_ = final_;
        c.abstract_ = abstract_;
        c.parent = parent.copy();
        interfaces.forEach(i -> c.interfaces.add(i.copy()));
        methods.forEach(m -> c.methods.add(m.copy()));
        return c;
    }

    @Nullable
    public String getParentName() {
        return getParent().getIdentifier();
    }
}
