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

/**
 * Created by weigl on 16.12.16.
 */
class DataTypeOptions(val map: MutableMap<String, String> = HashMap()) {
    val widthInt: Int by map.convert(16) { it.toInt() }
    val widthUInt: Int by map.convert(16) { it.toInt() }
    val widthSInt: Int by map.convert(8) { it.toInt() }
    val widthUSInt: Int by map.convert(8) { it.toInt() }
    val widthLInt: Int by map.convert(32) { it.toInt() }
    val widthULInt: Int by map.convert(32) { it.toInt() }
    val widthDInt: Int by map.convert(64) { it.toInt() }
    val widthUDInt: Int by map.convert(64) { it.toInt() }
}