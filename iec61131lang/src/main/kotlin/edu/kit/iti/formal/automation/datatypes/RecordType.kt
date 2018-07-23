package edu.kit.iti.formal.automation.datatypes

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.values.RecordValue
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
data class RecordType(override var name: String, val fields: VariableScope = VariableScope())
    : AnyDt(name) {

    fun addField(name: String, dataType: AnyDt) = fields.add(VariableDeclaration(name, dataType))

    override fun repr(obj: Any): String {
        val record = obj as RecordValue
        return record.fieldValues.entries
                .joinToString(", ", "(", ")") { (k, v) ->
                    k + "=" + v.dataType.repr(v.value)
                }
    }

    override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
}
