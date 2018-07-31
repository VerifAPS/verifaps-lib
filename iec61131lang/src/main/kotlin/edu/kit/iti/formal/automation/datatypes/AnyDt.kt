package edu.kit.iti.formal.automation.datatypes

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

import edu.kit.iti.formal.automation.st.Identifiable

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
abstract class AnyDt : Identifiable {
    object VOID : AnyDt() {
        override fun repr(obj: Any): String {
            TODO("not implemented")
        }

        override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
            TODO("not implemented")
        }

        init {
            name = "VOID"
        }
    }

    override var name: String = "ANY"

    protected constructor() {
        name = javaClass.getSimpleName().toUpperCase()
    }

    protected constructor(name: String) {
        this.name = name
    }

    abstract fun repr(obj: Any): String

    abstract fun <T> accept(visitor: DataTypeVisitorNN<T>): T

    override fun toString() = name
    open fun reprDecl(): String = "n/a"

    fun isAnonym(): Boolean = name.equals(ANONYM_DATATYPE)

    companion object {
        val ANONYM_DATATYPE = "ANONYM"
    }

}

