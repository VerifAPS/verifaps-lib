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

package edu.kit.iti.formal.automation.datatypes;

import edu.kit.iti.formal.automation.st.ast.InterfaceDeclaration;
import lombok.AllArgsConstructor;
import lombok.Data;

/**
 * @author Augusto Modanese
 */
@Data
@AllArgsConstructor
public class InterfaceDataType extends Any {
    private InterfaceDeclaration interfaceDeclaration;

    @Override
    public String repr(Object obj) {
        return "INTERFACE " + interfaceDeclaration.getName();
    }

    @Override public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
