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

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.IECString;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class StringTypeDeclaration extends TypeDeclaration<ScalarValue<? extends IECString, String>> {
    private ScalarValue<? extends AnyInt, Long> size;

    /**
     * <p>Getter for the field <code>size</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.values.ScalarValue} object.
     */
    public ScalarValue<? extends AnyInt, Long> getSize() {
        return size;
    }

    /**
     * <p>Setter for the field <code>size</code>.</p>
     *
     * @param size a {@link edu.kit.iti.formal.automation.datatypes.values.ScalarValue} object.
     */
    public void setSize(ScalarValue<? extends AnyInt, Long> size) {
        this.size = size;
    }

    /** {@inheritDoc} */
    @Override
    public Any getDataType(GlobalScope globalScope) {
        //TODO
        setBaseType(IECString.STRING_16BIT);
        return getBaseType();
    }

    @Override public StringTypeDeclaration clone() {
        StringTypeDeclaration t = new StringTypeDeclaration();
        t.initialization = initialization.clone();
        t.typeName = typeName;
        t.baseType = baseType;
        t.baseTypeName = baseTypeName;
        t.size = size.clone();
        return t;
    }

    /** {@inheritDoc} */
    @Override
    public <S> S visit(Visitor<S> visitor) {
        return visitor.visit(this);
    }
}
