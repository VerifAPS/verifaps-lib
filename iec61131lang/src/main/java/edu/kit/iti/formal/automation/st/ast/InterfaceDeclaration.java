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
import edu.kit.iti.formal.automation.st.Identifiable;
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Augusto Modanese
 */
@Data
@EqualsAndHashCode(exclude = "methods", callSuper = true)
@NoArgsConstructor
public final class InterfaceDeclaration extends TopLevelScopeElement<IEC61131Parser.Interface_declarationContext> implements Identifiable {
    protected List<IdentifierPlaceHolder<InterfaceDeclaration>> interfaces = new ArrayList<>();
    protected List<MethodDeclaration> methods = new ArrayList<>();
    protected String name = "";

    @Override
    public String getIdentifier() {
        return name;
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
