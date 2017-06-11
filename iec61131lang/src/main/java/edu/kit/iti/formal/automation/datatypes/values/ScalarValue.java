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

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.Initialization;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 11.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class ScalarValue<T extends Any, S> extends Initialization
        implements Value<T> {
    private T dataType;
    private S value;


    /**
     * <p>Constructor for ScalarValue.</p>
     *
     * @param dataType a T object.
     * @param value a S object.
     */
    public ScalarValue(T dataType, S value) {
        this.dataType = dataType;
        this.value = value;
    }

    /** {@inheritDoc} */
    @Override
    public T getDataType() {
        return dataType;
    }

    /**
     * <p>Setter for the field <code>dataType</code>.</p>
     *
     * @param dataType a T object.
     */
    public void setDataType(T dataType) {
        this.dataType = dataType;
    }

    /**
     * <p>Getter for the field <code>value</code>.</p>
     *
     * @return a S object.
     */
    public S getValue() {
        return value;
    }

    /**
     * <p>Setter for the field <code>value</code>.</p>
     *
     * @param value a S object.
     */
    public void setValue(S value) {
        this.value = value;
    }

    /** {@inheritDoc} */
    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override public ScalarValue<T, S> clone() {
        ScalarValue<T, S> sv = new ScalarValue<T, S>(dataType, value);
        return sv;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return "ScalarValue{" +
                "dataType=" + dataType +
                ", value=" + value +
                '}';
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ScalarValue)) return false;

        ScalarValue that = (ScalarValue) o;

        if (dataType != null ? !dataType.equals(that.dataType) : that.dataType != null) return false;
        if (value != null ? !value.equals(that.value) : that.value != null) return false;

        return true;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        int result = dataType != null ? dataType.hashCode() : 0;
        result = 31 * result + (value != null ? value.hashCode() : 0);
        return result;
    }

    /** {@inheritDoc} */
    @Override
    public Any dataType(LocalScope localScope) {
        return getDataType();
    }
}
