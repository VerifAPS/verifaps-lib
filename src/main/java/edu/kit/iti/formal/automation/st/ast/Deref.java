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

import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 02.08.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class Deref extends Reference {
    private Reference reference;

    /**
     * <p>Constructor for Deref.</p>
     *
     * @param reference a {@link edu.kit.iti.formal.automation.st.ast.Reference} object.
     */
    public Deref(Reference reference) {
        this.reference = reference;
    }

    /**
     * <p>Getter for the field <code>reference</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Reference} object.
     */
    public Reference getReference() {
        return reference;
    }

    /**
     * <p>Setter for the field <code>reference</code>.</p>
     *
     * @param reference a {@link edu.kit.iti.formal.automation.st.ast.Reference} object.
     */
    public void setReference(Reference reference) {
        this.reference = reference;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return reference + "^";
    }

    /** {@inheritDoc} */
    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public Any dataType(LocalScope localScope) {
        return null;//TODO
    }
}
