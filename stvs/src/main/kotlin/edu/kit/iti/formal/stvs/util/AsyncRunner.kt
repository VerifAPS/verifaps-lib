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
package edu.kit.iti.formal.stvs.util

/**
 * This interface represents the action that should be executed while a
 * [JavaFxAsyncTask] is running an that depends on a process.
 */
interface AsyncRunner<T> {
    /**
     * This method must be implemented to define what the [JavaFxAsyncTask] is doing
     * while running.
     *
     * @return Object of type `T` that is computed by this method
     * @throws Exception exception while running
     */
    @Throws(Exception::class)
    fun run(): T

    fun terminate()
}