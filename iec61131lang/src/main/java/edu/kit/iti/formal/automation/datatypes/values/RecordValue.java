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

import edu.kit.iti.formal.automation.datatypes.RecordType;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class RecordValue {
    private RecordType recordType;
    private Map<String, RuntimeVariable> fieldValues = new HashMap<>();

    /**
     * <p>Constructor for RecordValue.</p>
     *
     * @param recordType a {@link edu.kit.iti.formal.automation.datatypes.RecordType} object.
     */
    public RecordValue(RecordType recordType) {
        this.recordType = recordType;

        for (VariableDeclaration field : recordType.getFields()) {
            fieldValues.put(field.getName(),
                    new RuntimeVariable(field.getName(),
                            field.getTypeDeclaration().getInitialization(), field.getDataType())
            );
        }
    }

    /**
     * <p>Getter for the field <code>fieldValues</code>.</p>
     *
     * @return a {@link java.util.Map} object.
     */
    public Map<String, RuntimeVariable> getFieldValues() {
        return fieldValues;
    }

    /**
     * <p>Setter for the field <code>fieldValues</code>.</p>
     *
     * @param fieldValues a {@link java.util.Map} object.
     */
    public void setFieldValues(Map<String, RuntimeVariable> fieldValues) {
        this.fieldValues = fieldValues;
    }
}
