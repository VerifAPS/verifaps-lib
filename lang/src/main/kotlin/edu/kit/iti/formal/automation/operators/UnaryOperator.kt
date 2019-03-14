package edu.kit.iti.formal.automation.operators

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

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.AnyInt

class UnaryOperator(override val symbol: String, val validFor: AnyDt) : Operator {
    override val expectedDataTypes: Array<AnyDt>
        get() = arrayOf(validFor)


    fun isValid(a: AnyDt): Boolean {
        return validFor.javaClass.isAssignableFrom(a.javaClass)
    }

    fun getPromotedType(a: AnyDt): AnyDt? {
        return if (isValid(a)) {
            if (a is AnyInt)
                a.asSigned()
            else a
        } else null
    }

    override fun equals(o: Any?): Boolean {
        if (this === o) return true
        if (o == null || javaClass != o.javaClass) return false
        val that = o as UnaryOperator?
        return symbol == that!!.symbol
    }

    override fun hashCode() = symbol.hashCode()
}
