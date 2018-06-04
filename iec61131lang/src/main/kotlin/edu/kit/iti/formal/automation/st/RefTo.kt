package edu.kit.iti.formal.automation.st

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

import edu.kit.iti.formal.automation.st.Cloneable

/**
 * @param <T> an class which is identifiable
 * @author Alexander Weigl
 * @since 04.03.2017
</T> */
data class RefTo<T : Identifiable>(private var name: String?, private var identified: T?) : Cloneable<RefTo<*>> {
    var identifier: String?
        get() = if (obj != null) obj!!.name else name
        set(new) {
            this.name = new
        }

    var obj: T?
        get() = identified
        set(value) {
            // TODO: assertion should be changed
            //assert name == null || obj == null || obj.getName().equals(name);
            this.obj = value
        }


    val isIdentified: Boolean
        get() = obj != null

    constructor() : this(null, null)
    constructor(identifier: String) : this(identifier, null)
    constructor(obj: T) : this(obj.name, obj)

    override fun clone(): RefTo<T> = RefTo(identifier, obj)
}