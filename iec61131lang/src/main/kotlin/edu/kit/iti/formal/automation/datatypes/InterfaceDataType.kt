/*
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

package edu.kit.iti.formal.automation.datatypes

import edu.kit.iti.formal.automation.st.ast.InterfaceDeclaration
import lombok.AllArgsConstructor
import lombok.Data

/**
 * @author Augusto Modanese
 */
@Data
@AllArgsConstructor
class InterfaceDataType : RecordType {
    var interfaceDeclaration: InterfaceDeclaration? = null
        set(interfaceDeclaration) {
            field = this.interfaceDeclaration
        }

    override fun getName(): String {
        return this.interfaceDeclaration!!.name
    }

    override fun repr(obj: Any): String? {
        return "INTERFACE " + this.interfaceDeclaration!!.name
    }

    override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
        return visitor.visit(this)
    }
}
