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
import edu.kit.iti.formal.automation.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * <p>IdentifierInitializer class.</p>
 *
 * @author Alexander Weigl
 * @version 1 (16.12.16)
 */
public class IdentifierInitializer extends Initialization {
    private EnumerateType enumType;
    private String value;

    /**
     * <p>Constructor for IdentifierInitializer.</p>
     */
    public IdentifierInitializer() {
    }

    /**
     * <p>Constructor for IdentifierInitializer.</p>
     *
     * @param value a {@link java.lang.String} object.
     */
    public IdentifierInitializer(String value) {
        this.value = value;
    }

    /**
     * <p>Getter for the field <code>enumType</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.EnumerateType} object.
     */
    public EnumerateType getEnumType() {
        return enumType;
    }

    /**
     * <p>Setter for the field <code>enumType</code>.</p>
     *
     * @param enumType a {@link edu.kit.iti.formal.automation.datatypes.EnumerateType} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.IdentifierInitializer} object.
     */
    public IdentifierInitializer setEnumType(EnumerateType enumType) {
        this.enumType = enumType;
        return this;
    }

    /**
     * <p>Getter for the field <code>value</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getValue() {
        return value;
    }

    /**
     * <p>Setter for the field <code>value</code>.</p>
     *
     * @param value a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.IdentifierInitializer} object.
     */
    public IdentifierInitializer setValue(String value) {
        this.value = value;
        return this;
    }

    /** {@inheritDoc} */
    @Override
    public AnyDt dataType(Scope localScope) throws VariableNotDefinedException, TypeConformityException {
        return enumType;
    }

    @Override public IdentifierInitializer copy() {
        return new IdentifierInitializer(value).setEnumType(enumType);
    }

    /** {@inheritDoc} */
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
