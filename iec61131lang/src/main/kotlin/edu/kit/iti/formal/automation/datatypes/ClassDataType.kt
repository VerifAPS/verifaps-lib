package edu.kit.iti.formal.automation.datatypes

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.oo.OOUtils
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.ClassDeclaration
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import lombok.AllArgsConstructor
import lombok.Data
import lombok.EqualsAndHashCode

import java.util.stream.Collectors

/**
 * This data type represents a class.
 *
 * @author Alexander Weigl, Augusto Modanese
 * @version 1
 * @since 04.03.17
 */
@Data
@EqualsAndHashCode(callSuper = false)
@AllArgsConstructor
class ClassDataType : RecordType {
    val clazz: ClassDeclaration

    override var fields: Scope
        get() = Scope(OOUtils.getEffectiveScope(clazz).parallelStream()
                .map<VariableDeclaration>(Function<VariableDeclaration, VariableDeclaration> { it.copy() })
                .collect<List<VariableDeclaration>, Any>(Collectors.toList()))
        set(value: Scope) {
            super.fields = value
        }

    override fun repr(obj: Any): String? {
        return null
    }

    override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
        return visitor.visit(this)
    }

    override fun getName(): String {
        return clazz.name
    }
}
