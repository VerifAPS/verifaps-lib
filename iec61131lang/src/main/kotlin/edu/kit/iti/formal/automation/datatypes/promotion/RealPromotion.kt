package edu.kit.iti.formal.automation.datatypes.promotion

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
import edu.kit.iti.formal.automation.datatypes.AnyReal

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
class RealPromotion : TypePromotion {

    /** {@inheritDoc}  */
    override fun getPromotion(a: AnyDt, b: AnyDt): AnyDt? {
        try {
            return promote(a as AnyReal, b as AnyReal)
        } catch (e: ClassCastException) {
            try {
                return promote(a as AnyReal, b as AnyInt)
            } catch (e1: ClassCastException) {
                try {
                    return promote(b as AnyReal, a as AnyInt)
                } catch (e2: ClassCastException) {
                    return null
                }

            }

        }

    }

    private fun promote(a: AnyReal, b: AnyInt): AnyDt {
        return a
    }

    private fun promote(a: AnyReal, b: AnyReal): AnyDt? {
        return if (a == b) a else a as? AnyReal.LREAL ?: b
    }

    companion object {

        /** Constant `INSTANCE`  */
        val INSTANCE: TypePromotion = RealPromotion()
    }
}
