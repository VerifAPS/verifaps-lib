/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
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
 * *****************************************************************/
package edu.kit.iti.formal.automation.operators

import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.AnyNum
import edu.kit.iti.formal.automation.datatypes.promoteWith

/**
 * BinaryOperator represents a binary operator, e.g. addition +, multiply *, etc.
 *
 * Created on 24.11.16.
 *
 * @author Alexander Weigl
 * @version 1
 */
open class BinaryOperator(override val symbol: String, private val validType: AnyDt) : Operator {
    override val expectedDataTypes: Array<AnyDt>
        get() = arrayOf(validType, validType)

    fun isTypeConform(argument: AnyDt): Boolean = argument.isAssignableTo(validType)

    open fun getDataType(left: AnyDt, right: AnyDt): AnyDt? = left promoteWith right

    override fun equals(o: Any?): Boolean {
        if (this === o) return true
        if (o == null || javaClass != o.javaClass) return false
        val that = o as BinaryOperator?
        return symbol == that!!.symbol
    }

    override fun hashCode(): Int = symbol.hashCode()
}

class ComparisonOperator internal constructor(symbol: String) : BinaryOperator(symbol, AnyNum()) {
    override fun getDataType(left: AnyDt, right: AnyDt): AnyDt? = AnyBit.BOOL
}

class BooleanOperator internal constructor(symbol: String) : BinaryOperator(symbol, AnyBit.BOOL) {
    override fun getDataType(left: AnyDt, right: AnyDt): AnyDt? = AnyBit.BOOL
}