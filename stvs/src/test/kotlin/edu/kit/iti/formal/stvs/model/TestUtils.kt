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
package edu.kit.iti.formal.stvs.model

/**
 * Created by Philipp on 20.01.2017.
 */
object TestUtils {
    fun <T> collectionsEqual(`as`: Collection<T>?, bs: Collection<T>?): Boolean {
        if (`as` === bs) {
            return true
        }
        if (`as` == null || bs == null) {
            return false
        }
        if (`as`.size != bs.size) {
            return false
        }

        return `as`.stream().allMatch { elem: T -> bs.stream().anyMatch { obj: T -> elem!!.equals(obj) } }
    }

    fun <T> assertCollectionsEqual(`as`: Collection<T>?, bs: Collection<T>?) {
        if (!collectionsEqual(`as`, bs)) {
            val error = String.format(
                "Unequal collections: %n" +
                    "Expected: %s%n" +
                    "Actual  : %s%n",
                `as`,
                bs,
            )
            throw AssertionError(error)
        }
    }

    @Throws(Throwable::class)
    fun rethrowThreadUncheckedExceptions(runnable: Runnable) {
        val throwable = arrayOfNulls<Throwable>(1)
        val exceptionHandlerBefore = Thread.currentThread().uncaughtExceptionHandler
        Thread.currentThread().uncaughtExceptionHandler = Thread.UncaughtExceptionHandler { t, e -> throwable[0] = e }
        runnable.run()
        Thread.currentThread().uncaughtExceptionHandler = exceptionHandlerBefore
        if (throwable[0] != null) {
            throw throwable[0]!!
        }
    }
}