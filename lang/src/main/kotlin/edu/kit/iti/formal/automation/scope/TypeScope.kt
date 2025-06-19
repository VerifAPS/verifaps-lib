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
package edu.kit.iti.formal.automation.scope

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.AnyBit.*
import edu.kit.iti.formal.automation.st.Cloneable
import java.util.*

/**
 * Stores the available user defined/built-in datatypes
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
class TypeScope private constructor(private val impl: TreeMap<String, AnyDt> = TreeMap(String.CASE_INSENSITIVE_ORDER)) :
    MutableMap<String, AnyDt> by impl,
    Cloneable {

    fun register(vararg any: AnyDt) {
        for (a in any) {
            put(a.name, a)
        }
    }

    fun register(name: String, type: AnyDt) = put(name, type)

    override fun clone(): TypeScope {
        val ts = TypeScope()
        ts.putAll(this)
        return ts
    }

    companion object {
        fun empty(): TypeScope = TypeScope()

        fun builtin(): TypeScope {
            val e = empty()
            e.register(SINT, INT, LINT, DINT)
            e.register(USINT, UINT, ULINT, UDINT)
            e.register(BOOL, BYTE, LWORD, WORD, DWORD)
            e.register(IECString.WSTRING, IECString.STRING)
            e.register(
                AnyDate.TIME_OF_DAY,
                AnyDate.DATE_AND_TIME,
                AnyDate.DATE,
                TimeType.TIME_TYPE,
            )
            e.register(AnyReal.REAL, AnyReal.LREAL)
            e.register(VOID)
            return e
        }
    }
}
