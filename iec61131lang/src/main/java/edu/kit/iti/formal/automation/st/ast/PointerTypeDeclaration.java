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

import edu.kit.iti.formal.automation.datatypes.PointerType;
import edu.kit.iti.formal.automation.datatypes.values.PointerValue;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 24.11.16.
 * // TODO: 24.11.16  create everything
 *
 * @author weigl
 * @version $Id: $Id
 */
public class PointerTypeDeclaration
        extends TypeDeclaration<Literal> {
    /**
     * <p>Constructor for PointerTypeDeclaration.</p>
     *
     * @param pt a {@link java.lang.String} object.
     */
    public PointerTypeDeclaration(String pt) {
        setBaseTypeName(pt);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public PointerType getDataType(GlobalScope globalScope) {
        PointerType pt = new PointerType(super.getDataType(globalScope));
        baseType = pt;
        return pt;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <S> S accept(Visitor<S> visitor) {
        return visitor.visit(this);
    }

    public PointerTypeDeclaration copy() {
        PointerTypeDeclaration pt = new PointerTypeDeclaration(
                getBaseTypeName());
        return pt;
    }
}
