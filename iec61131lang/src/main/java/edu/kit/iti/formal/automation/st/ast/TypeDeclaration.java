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
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
@Data
@NoArgsConstructor
public abstract class TypeDeclaration<T extends Initialization> extends Top {
    protected String typeName;
    protected String baseTypeName;
    protected Any baseType;
    protected T initialization;

    /**
     * <p>Constructor for TypeDeclaration.</p>
     *
     * @param typeName a {@link java.lang.String} object.
     */
    public TypeDeclaration(String typeName) {
        this.typeName = typeName;
    }

    public TypeDeclaration(Any dataType) {
        this(dataType.getName());
    }

    /**
     * <p>Getter for the field <code>typeName</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getTypeName() {
        if (typeName == null) return baseTypeName;
        return typeName;
    }

    /** {@inheritDoc} */
    public abstract <S> S accept(Visitor<S> visitor);

    /**
     * <p>getDataType.</p>
     *
     * @param globalScope a {@link edu.kit.iti.formal.automation.scope.GlobalScope} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public Any getDataType(GlobalScope globalScope) {
        setBaseType(globalScope.resolveDataType(getBaseTypeName()));
        return getBaseType();
    }

    public abstract TypeDeclaration<T> copy();
}
