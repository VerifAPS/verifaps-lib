package edu.kit.iti.formal.automation.datatypes

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
            TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
        }

        override fun <T> accept(visitor: DataTypeVisitor<T>): T {
            TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
        }

        init {
            name = "VOID"
        }
    }

    override var name = "any"

    /**
     *
     * Constructor for AnyDt.
     */
    protected constructor() {
        name = javaClass.getSimpleName().toUpperCase()
    }

    /**
     *
     * Constructor for AnyDt.
     *
     * @param name a [java.lang.String] object.
     */
    protected constructor(name: String) {
        this.name = name
    }


    /**
     *
     * repr.
     *
     * @param obj a [java.lang.Object] object.
     * @return a [java.lang.String] object.
     */
    abstract fun repr(obj: Any): String

    /**
     *
     * accept.
     *
     * @param visitor a [edu.kit.iti.formal.automation.datatypes.DataTypeVisitor] object.
     * @param <T> a T object.
     * @return a T object.
    </T> */
    abstract fun <T> accept(visitor: DataTypeVisitor<T>): T
}
