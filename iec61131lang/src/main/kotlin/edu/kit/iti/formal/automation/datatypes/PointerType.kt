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

/**
 * Created by weigl on 01.08.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
class PointerType
/**
 *
 * Constructor for PointerType.
 *
 * @param dataType a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
 */
(internal var of: AnyDt) : AnyDt() {

    /** {@inheritDoc}  */
    override fun toString(): String {
        return of.toString() + "^"
    }


    /** {@inheritDoc}  */
    override fun repr(obj: Any): String {
        return "n/a"
    }


    /** {@inheritDoc}  */
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}
