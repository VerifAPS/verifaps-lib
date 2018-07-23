package edu.kit.iti.formal.automation.st.util

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
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
data class Tuple<S, T>(val a: S, val b: T) {
    companion object {
        fun <T, S> make(a: T, b: S): Tuple<T, S> {
            return Tuple(a, b)
        }
    }
}

sealed class Either<L, R> {
    data class Left<L, R>(val l: L) : Either<L, R>()
    data class Right<L, R>(val r: R) : Either<L, R>()

    infix fun <Rp> bind(f: (R) -> (Either<L, Rp>)): Either<L, Rp> {
        return when (this) {
            is Either.Left<L, R> -> Left<L, Rp>(this.l)
            is Either.Right<L, R> -> f(this.r)
        }
    }

    infix fun <Rp> seq(e: Either<L, Rp>): Either<L, Rp> = e

    companion object {
        fun <L, R> ret(a: R) = Either.Right<L, R>(a)
        fun <L, R> fail(msg: String): Either.Right<L, R> = throw Exception(msg)
    }
}
