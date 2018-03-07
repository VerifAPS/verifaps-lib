package edu.kit.iti.formal.automation.datatypes.values;

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

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class RuntimeVariable {
    private String name;
    private Object value;
    private AnyDt dataType;

    /**
     * <p>Constructor for RuntimeVariable.</p>
     *
     * @param name a {@link java.lang.String} object.
     */
    public RuntimeVariable(String name) {
        this.name = name;
    }

    /**
     * <p>Constructor for RuntimeVariable.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @param dataType a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     */
    public RuntimeVariable(String name, AnyDt dataType) {
        this.name = name;
        this.dataType = dataType;
    }

    /**
     * <p>Constructor for RuntimeVariable.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @param value a {@link java.lang.Object} object.
     * @param dataType a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     */
    public RuntimeVariable(String name, Object value, AnyDt dataType) {
        this.name = name;
        this.value = value;
        this.dataType = dataType;
    }

    /**
     * <p>Getter for the field <code>name</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getName() {
        return name;
    }

    /**
     * <p>Setter for the field <code>name</code>.</p>
     *
     * @param name a {@link java.lang.String} object.
     */
    public void setName(String name) {
        this.name = name;
    }

    /**
     * <p>Getter for the field <code>value</code>.</p>
     *
     * @return a {@link java.lang.Object} object.
     */
    public Object getValue() {
        return value;
    }

    /**
     * <p>Setter for the field <code>value</code>.</p>
     *
     * @param value a {@link java.lang.Object} object.
     */
    public void setValue(Object value) {
        this.value = value;
    }

    /**
     * <p>Getter for the field <code>dataType</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     */
    public AnyDt getDataType() {
        return dataType;
    }

    /**
     * <p>Setter for the field <code>dataType</code>.</p>
     *
     * @param dataType a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     */
    public void setDataType(AnyDt dataType) {
        this.dataType = dataType;
    }
}
