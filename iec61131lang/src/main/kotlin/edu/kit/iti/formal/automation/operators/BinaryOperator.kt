package edu.kit.iti.formal.automation.operators

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

import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.promotion.DefaultTypePromoter
import edu.kit.iti.formal.automation.datatypes.promotion.TypePromotion

/**
 * BinaryOperator represents a binary operator, e.g. addition +, multiply *, etc.
 *
 * Created on 24.11.16.
 *
 * @author Alexander Weigl
 * @version 1
 */
open class BinaryOperator(override val symbol: String, private val validType: AnyDt) : Operator {
    protected var promoter: TypePromotion = DefaultTypePromoter()
    override val expectedDataTypes: Array<AnyDt>
        get() = arrayOf(validType, validType)

    /**
     *
     * isTypeConform.
     *
     * @param argument a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
     * @return a boolean.
     */
    fun isTypeConform(argument: AnyDt): Boolean {
        return argument.javaClass.isAssignableFrom(validType.javaClass)
    }

    fun getPromotedType(left: AnyDt, right: AnyDt): AnyDt? {
        return promoter.getPromotion(left, right)
    }


    override fun equals(o: Any?): Boolean {
        if (this === o) return true
        if (o == null || javaClass != o.javaClass) return false
        val that = o as BinaryOperator?
        return symbol == that!!.symbol
    }

    override fun hashCode(): Int = symbol.hashCode()
}
