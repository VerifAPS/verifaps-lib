package edu.kit.iti.formal.automation.datatypes.values

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
 * DateAndTimeData class.
 *
 * @author weigl
 * @version $Id: $Id
 */
class DateAndTimeData {
    /**
     *
     * Getter for the field `date`.
     *
     * @return a [DateData] object.
     */
    /**
     *
     * Setter for the field `date`.
     *
     * @param date a [DateData] object.
     */
    var date = DateData()
    /**
     *
     * Getter for the field `tod`.
     *
     * @return a [TimeofDayData] object.
     */
    /**
     *
     * Setter for the field `tod`.
     *
     * @param tod a [TimeofDayData] object.
     */
    var tod = TimeofDayData()

    /**
     *
     * getHours.
     *
     * @return a int.
     */
    /**
     *
     * setHours.
     *
     * @param hours a int.
     */
    var hours: Int
        get() = tod.hours
        set(hours) {
            tod.hours = hours
        }

    /**
     *
     * getMinutes.
     *
     * @return a int.
     */
    /**
     *
     * setMinutes.
     *
     * @param minutes a int.
     */
    var minutes: Int
        get() = tod.minutes
        set(minutes) {
            tod.minutes = minutes
        }

    /**
     *
     * getSeconds.
     *
     * @return a int.
     */
    /**
     *
     * setSeconds.
     *
     * @param seconds a int.
     */
    var seconds: Int
        get() = tod.seconds
        set(seconds) {
            tod.seconds = seconds
        }

    /**
     *
     * getYear.
     *
     * @return a int.
     */
    /**
     *
     * setYear.
     *
     * @param year a int.
     */
    var year: Int
        get() = date.year
        set(year) {
            date.year = year
        }

    /**
     *
     * getDay.
     *
     * @return a int.
     */
    /**
     *
     * setDay.
     *
     * @param day a int.
     */
    var day: Int
        get() = date.day
        set(day) {
            date.day = day
        }

    /**
     *
     * getMonth.
     *
     * @return a int.
     */
    /**
     *
     * setMonth.
     *
     * @param month a int.
     */
    var month: Int
        get() = date.month
        set(month) {
            date.month = month
        }

    /**
     *
     * getMillieSeconds.
     *
     * @return a int.
     */
    val millieSeconds: Int
        get() = tod.millieseconds

    /**
     *
     * Constructor for DateAndTimeData.
     *
     * @param date a [DateData] object.
     * @param tod a [TimeofDayData] object.
     */
    constructor(date: DateData, tod: TimeofDayData) {
        this.date = date
        this.tod = tod
    }

    /**
     *
     * Constructor for DateAndTimeData.
     *
     * @param years a int.
     * @param months a int.
     * @param days a int.
     * @param hours a int.
     * @param minutes a int.
     * @param seconds a int.
     */
    constructor(years: Int, months: Int, days: Int, hours: Int, minutes: Int, seconds: Int) {
        year = years
        month = months
        day = days
        hours = hours
        minutes = minutes
        seconds = seconds
    }

    /** {@inheritDoc}  */
    override fun toString(): String {
        return "DateAndTimeData{" +
                "date=" + date +
                ", tod=" + tod +
                '}'.toString()
    }

    /** {@inheritDoc}  */
    override fun equals(o: Any?): Boolean {
        if (this === o) return true
        if (o !is DateAndTimeData) return false

        val that = o as DateAndTimeData?

        return if (date != that!!.date) false else tod == that.tod
    }

    /** {@inheritDoc}  */
    override fun hashCode(): Int {
        var result = date.hashCode()
        result = 31 * result + tod.hashCode()
        return result
    }
}
