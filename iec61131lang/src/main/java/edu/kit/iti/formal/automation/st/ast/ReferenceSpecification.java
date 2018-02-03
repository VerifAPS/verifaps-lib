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

import edu.kit.iti.formal.automation.datatypes.ReferenceType;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * @author Augusto Modanese
 */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class ReferenceSpecification extends TypeDeclaration<Initialization> {
    private TypeDeclaration refTo;

    @Override
    public String getTypeName() {
        return "REF_TO "  + refTo.getTypeName();
    }

    @Override
    public ReferenceType getDataType(Scope globalScope) {
        ReferenceType rt = new ReferenceType(globalScope.resolveDataType(refTo.getTypeName()));
        baseType = rt;
        return rt;
    }

    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public ReferenceSpecification copy() {
        ReferenceSpecification rs = new ReferenceSpecification();
        rs.refTo = refTo;
        rs.baseType = baseType;
        return rs;
    }
}
