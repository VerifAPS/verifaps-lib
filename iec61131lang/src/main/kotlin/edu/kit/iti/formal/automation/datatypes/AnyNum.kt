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

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
open class AnyNum : AnyDt() {

    /** {@inheritDoc}  */
    override fun repr(obj: Any): String {
        throw IllegalStateException("No repr for AnyNum")
    }

    /** {@inheritDoc}  */
    override fun toString(): String {
        return "ANY_NUM"
    }


    /** {@inheritDoc}  */
    override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
        return visitor.visit(this)
    }

    companion object {
        /** Constant `ANY_NUM`  */
        val ANY_NUM: AnyDt = AnyNum()
    }
}
