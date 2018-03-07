package edu.kit.iti.formal.automation.st.ast;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
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

import edu.kit.iti.formal.automation.datatypes.AnyDt;
import edu.kit.iti.formal.automation.datatypes.IECString;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
@Data
public class StringTypeDeclaration extends TypeDeclaration<Literal> {
    private Literal size;


    /** {@inheritDoc} */
    @Override
    public AnyDt getDataType(Scope globalScope) {
        //TODO
        setBaseType(IECString.STRING_16BIT);
        return getBaseType();
    }

    @Override public StringTypeDeclaration copy() {
        StringTypeDeclaration t = new StringTypeDeclaration();
        t.initialization = initialization.copy();
        t.typeName = typeName;
        t.baseType = baseType;
        t.baseTypeName = baseTypeName;
        t.size = size.copy();
        return t;
    }

    /** {@inheritDoc} */
    @Override
    public <S> S accept(Visitor<S> visitor) {
        return visitor.visit(this);
    }
}
