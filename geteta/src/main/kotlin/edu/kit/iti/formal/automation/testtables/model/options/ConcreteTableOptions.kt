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
package edu.kit.iti.formal.automation.testtables.model.options

import edu.kit.iti.formal.automation.testtables.model.Duration

/**
 * Created by weigl on 16.12.16.
 */
class ConcreteTableOptions(val properties: MutableMap<String, String>) {

    fun getCount(step: String, defaultValue: Duration): Int =
        properties["cycles.$step"]?.toInt() ?: when (defaultValue) {
            is Duration.Omega -> 10
            is Duration.OpenInterval -> defaultValue.lower
            is Duration.ClosedInterval -> (defaultValue.lower + defaultValue.upper) / 2
        }
}