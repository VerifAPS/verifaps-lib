package edu.kit.iti.formal.automation.datatypes.values;

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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

/**
 * <p>DateAndTimeData class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class DateAndTimeData {
    private DateData date = new DateData();
    private TimeofDayData tod = new TimeofDayData();

    /**
     * <p>Constructor for DateAndTimeData.</p>
     *
     * @param date a {@link DateData} object.
     * @param tod a {@link TimeofDayData} object.
     */
    public DateAndTimeData(DateData date, TimeofDayData tod) {
        this.date = date;
        this.tod = tod;
    }

    /**
     * <p>Constructor for DateAndTimeData.</p>
     *
     * @param years a int.
     * @param months a int.
     * @param days a int.
     * @param hours a int.
     * @param minutes a int.
     * @param seconds a int.
     */
    public DateAndTimeData(int years, int months, int days, int hours, int minutes, int seconds) {
        setYear(years);
        setMonth(months);
        setDay(days);
        setHours(hours);
        setMinutes(minutes);
        setSeconds(seconds);
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return "DateAndTimeData{" +
                "date=" + date +
                ", tod=" + tod +
                '}';
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof DateAndTimeData)) return false;

        DateAndTimeData that = (DateAndTimeData) o;

        if (!date.equals(that.date)) return false;
        return tod.equals(that.tod);
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        int result = date.hashCode();
        result = 31 * result + tod.hashCode();
        return result;
    }

    /**
     * <p>Getter for the field <code>date</code>.</p>
     *
     * @return a {@link DateData} object.
     */
    public DateData getDate() {
        return date;
    }

    /**
     * <p>Setter for the field <code>date</code>.</p>
     *
     * @param date a {@link DateData} object.
     */
    public void setDate(DateData date) {
        this.date = date;
    }

    /**
     * <p>Getter for the field <code>tod</code>.</p>
     *
     * @return a {@link TimeofDayData} object.
     */
    public TimeofDayData getTod() {
        return tod;
    }

    /**
     * <p>Setter for the field <code>tod</code>.</p>
     *
     * @param tod a {@link TimeofDayData} object.
     */
    public void setTod(TimeofDayData tod) {
        this.tod = tod;
    }

    /**
     * <p>setSeconds.</p>
     *
     * @param seconds a int.
     */
    public void setSeconds(int seconds) {
        tod.setSeconds(seconds);
    }

    /**
     * <p>getHours.</p>
     *
     * @return a int.
     */
    public int getHours() {
        return tod.getHours();
    }

    /**
     * <p>setHours.</p>
     *
     * @param hours a int.
     */
    public void setHours(int hours) {
        tod.setHours(hours);
    }

    /**
     * <p>getMinutes.</p>
     *
     * @return a int.
     */
    public int getMinutes() {
        return tod.getMinutes();
    }

    /**
     * <p>setMinutes.</p>
     *
     * @param minutes a int.
     */
    public void setMinutes(int minutes) {
        tod.setMinutes(minutes);
    }

    /**
     * <p>getSeconds.</p>
     *
     * @return a int.
     */
    public int getSeconds() {
        return tod.getSeconds();
    }

    /**
     * <p>getYear.</p>
     *
     * @return a int.
     */
    public int getYear() {
        return date.getYear();
    }

    /**
     * <p>setDay.</p>
     *
     * @param day a int.
     */
    public void setDay(int day) {
        date.setDay(day);
    }

    /**
     * <p>setMonth.</p>
     *
     * @param month a int.
     */
    public void setMonth(int month) {
        date.setMonth(month);
    }

    /**
     * <p>setYear.</p>
     *
     * @param year a int.
     */
    public void setYear(int year) {
        date.setYear(year);
    }

    /**
     * <p>getDay.</p>
     *
     * @return a int.
     */
    public int getDay() {
        return date.getDay();
    }

    /**
     * <p>getMonth.</p>
     *
     * @return a int.
     */
    public int getMonth() {
        return date.getMonth();
    }

    /**
     * <p>getMillieSeconds.</p>
     *
     * @return a int.
     */
    public int getMillieSeconds() {
        return tod.getMillieseconds();
    }
}
