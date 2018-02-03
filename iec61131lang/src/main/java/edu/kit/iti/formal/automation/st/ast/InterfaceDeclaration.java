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
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Augusto Modanese
 */
@Data
@NoArgsConstructor
public class InterfaceDeclaration extends Classifier<IEC61131Parser.Interface_declarationContext> {
    @Override
    public void setScope(Scope global) {
        super.setScope(global);
        for (IdentifierPlaceHolder<InterfaceDeclaration> interfaceDeclaration : interfaces)
            interfaceDeclaration.setIdentifiedObject(global.resolveInterface(interfaceDeclaration.getIdentifier()));
    }

    /**
     * To be called only after bound to global scope!
     *
     * @return The list of interfaces the interface extends.
     */
    public List<InterfaceDeclaration> getExtendedInterfaces() {
        List<InterfaceDeclaration> extendedInterfaces = interfaces.stream()
                .map(IdentifierPlaceHolder::getIdentifiedObject).collect(Collectors.toList());
        // Add extended interfaces
        for (InterfaceDeclaration interfaceDeclaration : extendedInterfaces)
            extendedInterfaces.addAll(interfaceDeclaration.getExtendedInterfaces());
        return extendedInterfaces;
    }

    @Override
    public InterfaceDeclaration copy() {
        InterfaceDeclaration i = new InterfaceDeclaration();
        i.name = name;
        methods.forEach(method -> i.methods.add(method.copy()));
        interfaces.forEach(intf -> i.interfaces.add(intf.copy()));
        return i;
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
