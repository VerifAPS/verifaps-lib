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
package edu.kit.iti.formal.stvs.model.expressions

/**
 * The runtime representation for intervals that possibly have no upper bound, but have a guaranteed
 * lower bound.
 *
 * @author Benjamin Alt
 */
data class LowerBoundedInterval
/**
 * Creates an instance of an interval.
 *
 * @param lowerBound the lower bound for this interval
 * @param upperBound the optional upper bound for this interval
 */
(
    val lowerBound: Int,
    val upperBound: Int? = null
) {
    init {
        require(lowerBound >= 0)
        upperBound?.let {
            require(it >= 0)
            require(it >= lowerBound)
        }
    }
}