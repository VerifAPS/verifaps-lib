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

import edu.kit.iti.formal.automation.ValueFactory;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.*;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class EnumerationTypeDeclaration extends TypeDeclaration<ScalarValue<EnumerateType, ?>> {
    private List<String> allowedValues = new LinkedList<>();
    private Map<String, ScalarValue<? extends AnyInt, Long>> values = new HashMap<>();
    private int counter = 0;

    /**
     * <p>Constructor for EnumerationTypeDeclaration.</p>
     */
    public EnumerationTypeDeclaration() {
        setBaseTypeName("ENUM");
    }

    /** {@inheritDoc} */
    @Override
    public <S> S visit(Visitor<S> visitor) {
        return visitor.visit(this);
    }

    /**
     * <p>addValue.</p>
     *
     * @param text a {@link java.lang.String} object.
     */
    public void addValue(String text) {
        allowedValues.add(text);
        values.put(text, ValueFactory.makeUInt(counter));
        counter++;
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
    }

    /** {@inheritDoc} */
    @Override
    public EnumerateType getDataType(GlobalScope globalScope) {
        String init = allowedValues.get(0);
        if (initialization != null && initialization.getValue() != null) {
            if (initialization.getValue() instanceof String) {
                String value = (String) initialization.getValue();
                init = value;
            } else if (initialization.getValue() instanceof Integer) {
                Integer value = (Integer) initialization.getValue();
                init = allowedValues.get(value);
            }
        }

        EnumerateType et = new EnumerateType(getTypeName(), allowedValues, init);
        setBaseType(et);
        return et;
    }

    @Override public EnumerationTypeDeclaration clone() {
        EnumerationTypeDeclaration etd = new EnumerationTypeDeclaration();
        etd.allowedValues = new ArrayList<>(allowedValues);
        etd.counter = counter;
        etd.baseType = baseType;
        etd.baseTypeName = baseTypeName;
        etd.values = new HashMap<>(values);
        etd.typeName = typeName;
        return etd;
    }

    /**
     * <p>setInt.</p>
     *
     * @param val a {@link edu.kit.iti.formal.automation.datatypes.values.ScalarValue} object.
     */
    public void setInt(ScalarValue<? extends AnyInt, Long> val) {
        values.put(allowedValues.get(allowedValues.size() - 1), val);
        counter = (int) (val.getValue() + 1);
    }
}
