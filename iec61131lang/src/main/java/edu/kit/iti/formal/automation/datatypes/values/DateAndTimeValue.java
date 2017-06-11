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
 * <p>DateAndTimeValue class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class DateAndTimeValue {
    private DateValue date = new DateValue();
    private TimeOfDayValue tod = new TimeOfDayValue();

    /**
     * <p>Constructor for DateAndTimeValue.</p>
     *
     * @param date a {@link edu.kit.iti.formal.automation.datatypes.values.DateValue} object.
     * @param tod a {@link edu.kit.iti.formal.automation.datatypes.values.TimeOfDayValue} object.
     */
    public DateAndTimeValue(DateValue date, TimeOfDayValue tod) {
        this.date = date;
        this.tod = tod;
    }

    /**
     * <p>Constructor for DateAndTimeValue.</p>
     *
     * @param years a int.
     * @param months a int.
     * @param days a int.
     * @param hours a int.
     * @param minutes a int.
     * @param seconds a int.
     */
    public DateAndTimeValue(int years, int months, int days, int hours, int minutes, int seconds) {
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
        return "DateAndTimeValue{" +
                "date=" + date +
                ", tod=" + tod +
                '}';
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof DateAndTimeValue)) return false;

        DateAndTimeValue that = (DateAndTimeValue) o;

        if (!date.equals(that.date)) return false;
        if (!tod.equals(that.tod)) return false;

        return true;
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
     * @return a {@link edu.kit.iti.formal.automation.datatypes.values.DateValue} object.
     */
    public DateValue getDate() {
        return date;
    }

    /**
     * <p>Setter for the field <code>date</code>.</p>
     *
     * @param date a {@link edu.kit.iti.formal.automation.datatypes.values.DateValue} object.
     */
    public void setDate(DateValue date) {
        this.date = date;
    }

    /**
     * <p>Getter for the field <code>tod</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.values.TimeOfDayValue} object.
     */
    public TimeOfDayValue getTod() {
        return tod;
    }

    /**
     * <p>Setter for the field <code>tod</code>.</p>
     *
     * @param tod a {@link edu.kit.iti.formal.automation.datatypes.values.TimeOfDayValue} object.
     */
    public void setTod(TimeOfDayValue tod) {
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
