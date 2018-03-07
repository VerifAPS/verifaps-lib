package edu.kit.iti.formal.automation.datatypes;

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

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class EnumerateType extends AnyDt {
    private String name;
    private List<String> allowedValues = new ArrayList<>();
    private String defValue;
    private int bitlength;

    /**
     * <p>Constructor for EnumerateType.</p>
     */
    public EnumerateType() {
        //the unknown type
    }

    /**
     * <p>Constructor for EnumerateType.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @param allowedValues a {@link java.util.List} object.
     */
    public EnumerateType(String name, List<String> allowedValues) {
        this(name, allowedValues, allowedValues.get(0));
    }

    /**
     * <p>Constructor for EnumerateType.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @param allowedValues a {@link java.util.List} object.
     * @param defValue a {@link java.lang.String} object.
     */
    public EnumerateType(String name, List<String> allowedValues, String defValue) {
        this.name = name;
        setAllowedValues(allowedValues);
        setDefValue(defValue);
    }

    /**
     * <p>Constructor for EnumerateType.</p>
     *
     * @param prefix a {@link java.lang.String} object.
     */
    public EnumerateType(String prefix) {
        this.name = prefix;
    }

    /**
     * <p>Getter for the field <code>name</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getName() {
        return name;
    }

    /** {@inheritDoc} */
    public void setName(String name) {
        this.name = name;
    }

    /**
     * <p>Getter for the field <code>allowedValues</code>.</p>
     *
     * @return a {@link java.util.List} object.
     */
    public List<String> getAllowedValues() {
        return allowedValues;
    }

    /**
     * <p>Setter for the field <code>allowedValues</code>.</p>
     *
     * @param allowedValues a {@link java.util.List} object.
     */
    public void setAllowedValues(List<String> allowedValues) {
        this.allowedValues = allowedValues;
        bitlength = (int) Math.ceil(Math.log(allowedValues.size()));
    }

    /**
     * <p>Getter for the field <code>defValue</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getDefValue() {
        return defValue;
    }

    /**
     * <p>Setter for the field <code>defValue</code>.</p>
     *
     * @param defValue a {@link java.lang.String} object.
     */
    public void setDefValue(String defValue) {
        assert isAllowedValue(defValue);
        this.defValue = defValue;
    }

    /** {@inheritDoc} */
    @Override
    public String repr(Object obj) {
        if (name == null) return String.valueOf(obj);
        else return name + "#" + obj;
    }


    /** {@inheritDoc} */
    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public boolean isAllowedValue(String value) {
        return allowedValues.contains(value);
    }

    @Override
    public String getIdentifier() {
        return name;
    }
}
