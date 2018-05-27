package edu.kit.iti.formal.automation.datatypes.promotion

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
import edu.kit.iti.formal.automation.datatypes.AnySignedInt
import edu.kit.iti.formal.automation.datatypes.AnyUnsignedInt

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
class IntegerPromotion : TypePromotion {

    /** {@inheritDoc}  */
    override fun getPromotion(a: AnyDt, b: AnyDt): AnyDt? {
        try {
            return promote(a as AnySignedInt, b as AnySignedInt)
        } catch (e: ClassCastException) {
            try {
                return promote(a as AnyUnsignedInt, b as AnyUnsignedInt)
            } catch (e1: ClassCastException) {
                try {
                    return promote(a as AnySignedInt, b as AnyUnsignedInt)
                } catch (e2: ClassCastException) {
                    try {
                        return promote(b as AnySignedInt, a as AnyUnsignedInt)
                    } catch (e3: ClassCastException) {
                        return null
                    }

                }

            }

        }

    }

    /**
     *
     * promote.
     *
     * @param a a [edu.kit.iti.formal.automation.datatypes.AnySignedInt] object.
     * @param b a [edu.kit.iti.formal.automation.datatypes.AnySignedInt] object.
     * @return a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
     */
    fun promote(a: AnySignedInt, b: AnySignedInt): AnyDt {
        return if (a.bitLength >= b.bitLength)
            a
        else
            b
    }


    /**
     *
     * promote.
     *
     * @param a a [AnyUnsignedInt] object.
     * @param b a [AnyUnsignedInt] object.
     * @return a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
     */
    fun promote(a: AnyUnsignedInt, b: AnyUnsignedInt): AnyDt {
        return if (a.bitLength >= b.bitLength)
            a
        else
            b
    }

    /**
     *
     * promote.
     *
     * @param a a [edu.kit.iti.formal.automation.datatypes.AnySignedInt] object.
     * @param b a [AnyUnsignedInt] object.
     * @return a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
     */
    fun promote(a: AnySignedInt, b: AnyUnsignedInt): AnyDt {
        return if (a.bitLength > b.bitLength)
            a
        else
            b.asSigned()
    }

    companion object {
        /** Constant `INSTANCE`  */
        val INSTANCE = IntegerPromotion()
    }
}
