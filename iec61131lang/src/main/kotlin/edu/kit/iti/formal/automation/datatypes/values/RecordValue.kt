package edu.kit.iti.formal.automation.datatypes.values

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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.RecordType
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration

import java.util.HashMap

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
class RecordValue
/**
 *
 * Constructor for RecordValue.
 *
 * @param recordType a [edu.kit.iti.formal.automation.datatypes.RecordType] object.
 */
(private val recordType: RecordType) {
    private var fieldValues: MutableMap<String, RuntimeVariable> = HashMap()

    init {

        for (field in recordType.fields) {
            fieldValues[field.name] = RuntimeVariable(field.name,
                    field.typeDeclaration!!.initialization, field.dataType)
        }
    }

    /**
     *
     * Getter for the field `fieldValues`.
     *
     * @return a [java.util.Map] object.
     */
    fun getFieldValues(): Map<String, RuntimeVariable> {
        return fieldValues
    }

    /**
     *
     * Setter for the field `fieldValues`.
     *
     * @param fieldValues a [java.util.Map] object.
     */
    fun setFieldValues(fieldValues: MutableMap<String, RuntimeVariable>) {
        this.fieldValues = fieldValues
    }
}
