package edu.kit.iti.formal.automation.scope

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

import edu.kit.iti.formal.automation.datatypes.*

import java.util.TreeMap

import edu.kit.iti.formal.automation.datatypes.AnyBit.*
import edu.kit.iti.formal.automation.datatypes.IECString.STRING_16BIT
import edu.kit.iti.formal.automation.datatypes.IECString.STRING_8BIT

/**
 * Stores the available user defined/built-in datatypes
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
class TypeScope private constructor() : TreeMap<String, AnyDt>() {

    /**
     *
     * register.
     *
     * @param any a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
     */
    fun register(vararg any: AnyDt) {
        for (a in any)
            put(a.name, a)
    }

    fun register(name: String, type: AnyDt?) {
        put(name, type)
    }

    override fun clone(): TypeScope {
        val ts = TypeScope()
        ts.putAll(this)
        return ts
    }

    companion object {

        /**
         *
         * empty.
         *
         * @return a [edu.kit.iti.formal.automation.scope.TypeScope] object.
         */
        fun empty(): TypeScope {
            return TypeScope()
        }

        /**
         *
         * builtin.
         *
         * @return a [edu.kit.iti.formal.automation.scope.TypeScope] object.
         */
        fun builtin(): TypeScope {
            val e = empty()
            e.register(DataTypes.SINT, DataTypes.INT, DataTypes.LINT, DataTypes.DINT)
            e.register(DataTypes.USINT, DataTypes.UINT, DataTypes.ULINT, DataTypes.UDINT)
            e.register(BOOL, BYTE, LWORD, WORD, DWORD)
            e.register(STRING_8BIT, STRING_16BIT)
            e.register(AnyDate.TIME_OF_DAY, AnyDate.DATE_AND_TIME, AnyDate.DATE,
                    TimeType.TIME_TYPE)
            e.register(AnyReal.REAL, AnyReal.LREAL)
            e.register("VOID", null)
            return e
        }
    }
}
