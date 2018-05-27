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
 *
 * Abstract IECString class.
 *
 * @author weigl
 * @version $Id: $Id
 */
abstract class IECString : AnyDt() {


    class WString : IECString() {
        override fun repr(obj: Any): java.lang.String {
            return "WSTRING#\"$obj\""
        }


        override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
            return visitor.visit(this)
        }
    }

    class String : IECString() {
        override fun repr(obj: Any): java.lang.String {
            return "WSTRING#'$obj'"
        }

        override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
            return visitor.visit(this)
        }
    }

    companion object {
        /** Constant `STRING_8BIT`  */
        val STRING_8BIT = String()
        /** Constant `STRING_16BIT`  */
        val STRING_16BIT = WString()
    }


}
