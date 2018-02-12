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

package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Augusto Modanese
 */
@Data
@EqualsAndHashCode(exclude = "methods")
@NoArgsConstructor
public class InterfaceDeclaration extends Classifier<IEC61131Parser.Interface_declarationContext> {
    private String name;
    private List<MethodDeclaration> methods = new ArrayList<>();
    private List<IdentifierPlaceHolder<InterfaceDeclaration>> extendsInterfaces = new ArrayList<>();

    @Override
    public String getIdentifier() {
        return name;
    }

    public void addExtends(String interfaze) {
        extendsInterfaces.add(new IdentifierPlaceHolder<>(interfaze));
    }

    public void setMethods(List<MethodDeclaration> methods) {
        for (MethodDeclaration methodDeclaration : methods)
            methodDeclaration.setParent(this);
        this.methods = methods;
    }

    /**
     * To be called only after bound to global scope!
     *
     * @return The list of interfaces the interface extends.
     */
    public List<InterfaceDeclaration> getExtendedInterfaces() {
        List<InterfaceDeclaration> extendedInterfaces = extendsInterfaces.stream()
                .map(i -> i.getIdentifiedObject()).collect(Collectors.toList());
        // Add extended interfaces
        for (InterfaceDeclaration interfaceDeclaration : new ArrayList<>(extendedInterfaces))
            extendedInterfaces.addAll(interfaceDeclaration.getExtendedInterfaces());
        return extendedInterfaces;
    }

    @Override
    public TopLevelScopeElement copy() {
        InterfaceDeclaration i = new InterfaceDeclaration();
        i.name = name;
        methods.forEach(method -> i.methods.add(method.copy()));
        extendsInterfaces.forEach(intf -> i.extendsInterfaces.add(intf.copy()));
        return i;
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public boolean hasMethod(String method) {
        return methods.stream().filter(m -> m.getName().equals(method)).findAny().isPresent();
    }

    public boolean hasMethodWithInheritance(String method) {
        if (hasMethod(method))
            return hasMethod(method);
        if (extendsInterfaces.isEmpty())
            return hasMethod(method);
        return extendsInterfaces.stream()
                .filter(i -> i.getIdentifiedObject().hasMethodWithInheritance(method))
                .findAny().isPresent();
    }

    public MethodDeclaration getMethod(String method) {
        if (hasMethod(method))
            return methods.stream().filter(m -> m.getName().equals(method)).findAny().get();
        return extendsInterfaces.stream()
                .filter(i -> i.getIdentifiedObject().hasMethodWithInheritance(method))
                .findAny().get().getIdentifiedObject().getMethod(method);
    }
}
