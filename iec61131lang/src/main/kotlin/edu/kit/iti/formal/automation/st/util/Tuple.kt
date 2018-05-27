package edu.kit.iti.formal.automation.st.util

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

import lombok.EqualsAndHashCode

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
@EqualsAndHashCode
class Tuple<S, T>
/**
 *
 * Constructor for Tuple.
 *
 * @param a a S object.
 * @param b a T object.
 */
(val a: S, val b: T) {

    override fun toString(): String {
        return a.toString() + "=" + b.toString()
    }

    companion object {

        /**
         *
         * make.
         *
         * @param a a T object.
         * @param b a S object.
         * @param <T> a T object.
         * @param <S> a S object.
         * @return a [edu.kit.iti.formal.automation.st.util.Tuple] object.
        </S></T> */
        fun <T, S> make(a: T, b: S): Tuple<T, S> {
            return Tuple(a, b)
        }
    }
}
