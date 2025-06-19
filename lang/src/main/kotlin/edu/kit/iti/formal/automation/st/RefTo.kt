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
package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
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

/**
 * @param <T> an class which isType identifiable
 * @author Alexander Weigl
 * @since 04.03.2017
</T> */
class RefTo<T : Identifiable>(private var name: String?, private var identified: T?) : Cloneable {
    var identifier: String?
        get() = if (obj != null) obj!!.name else name
        set(new) {
            this.name = new
        }

    var obj: T?
        get() = identified
        set(value) {
            //           if(value!=null || name == null || value?.name != name )
            //               throw IllegalStateException("Name does match the object name.")
            identified = value
        }

    val isIdentified: Boolean
        get() = obj != null

    constructor() : this(null, null)
    constructor(identifier: String?) : this(identifier, null)
    constructor(obj: T) : this(obj.name, obj)

    override fun clone(): RefTo<T> = RefTo(identifier, obj)
    fun resolve(func: (String) -> T?) {
        if (identifier != null) {
            try {
                obj = func(identifier!!)
            } catch (e: DataTypeNotDefinedException) {
            }
        }
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is RefTo<*>) return false

        if (identified != null && identified == other.identified) return true
        if (name == other.name) return true
        return false
    }

    override fun hashCode(): Int {
        var result = name?.hashCode() ?: 0
        result = 31 * result + (identified?.hashCode() ?: 0)
        return result
    }

    override fun toString(): String = "RefTo(name=$name, identified=$identified)"
}