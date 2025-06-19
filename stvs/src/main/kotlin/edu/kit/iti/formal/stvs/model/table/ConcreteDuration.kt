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
package edu.kit.iti.formal.stvs.model.table

/**
 * A concrete duration. A ConcreteDuration is localized in time, i.e. it is aware of the cycle in
 * which it begins.
 *
 * @author Benjamin Alt
 */
class ConcreteDuration(beginCycle: Int, duration: Int) {
    @JvmField
    val duration: Int

    @JvmField
    val beginCycle: Int

    /**
     * Construct a new concrete duration.
     *
     * @param beginCycle The cycle in which this duration begins
     * @param duration The duration
     */
    init {
        require(beginCycle >= 0) { "BeginCycle must be nonnegative" }
        require(duration >= 0) { "Duration must me nonnegative" }
        this.beginCycle = beginCycle
        this.duration = duration
    }

    val endCycle: Int
        get() = beginCycle + duration

    override fun toString(): String = duration.toString()

    override fun equals(o: Any?): Boolean {
        if (this === o) {
            return true
        }
        if (o == null || javaClass != o.javaClass) {
            return false
        }

        val duration1 = o as ConcreteDuration

        if (duration != duration1.duration) {
            return false
        }
        return beginCycle == duration1.beginCycle
    }

    override fun hashCode(): Int {
        var result = duration
        result = 31 * result + beginCycle
        return result
    }
}