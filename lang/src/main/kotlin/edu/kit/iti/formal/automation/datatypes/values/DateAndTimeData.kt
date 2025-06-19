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
package edu.kit.iti.formal.automation.datatypes.values

import edu.kit.iti.formal.automation.sfclang.split

data class DateAndTimeData(var date: DateData = DateData(), var tod: TimeofDayData = TimeofDayData()) {
    var hours: Int
        get() = tod.hours
        set(hours) {
            tod.hours = hours
        }

    var minutes: Int
        get() = tod.minutes
        set(minutes) {
            tod.minutes = minutes
        }

    var seconds: Int
        get() = tod.seconds
        set(seconds) {
            tod.seconds = seconds
        }

    var year: Int
        get() = date.year
        set(year) {
            date.year = year
        }

    var day: Int
        get() = date.day
        set(day) {
            date.day = day
        }

    var month: Int
        get() = date.month
        set(month) {
            date.month = month
        }

    var millieSeconds: Int
        get() = tod.millieseconds
        set(ms) {
            tod.millieseconds = ms
        }

    constructor(years: Int, months: Int, days: Int, hours: Int, minutes: Int, seconds: Int) :
        this(DateData(years, months, days), TimeofDayData(hours, minutes, seconds))

    companion object {
        fun parse(str: String): DateAndTimeData {
            val (_, _, value) = split(str)
            val a = value.substring(0, "yyyy-mm-dd".length)
            val b = value.substring("yyyy-mm-dd-".length)
            val date = DateData.parse(a)
            val tod = TimeofDayData.parse(b)
            return DateAndTimeData(date, tod)
        }
    }
}