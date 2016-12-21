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
 * <p>DateValue class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class DateValue {
    private int year, month, day;

    /**
     * <p>Constructor for DateValue.</p>
     *
     * @param year a int.
     * @param month a int.
     * @param day a int.
     */
    public DateValue(int year, int month, int day) {
        this.year = year;
        this.month = month;
        this.day = day;
    }

    /**
     * <p>Constructor for DateValue.</p>
     */
    public DateValue() {
        this(0, 1, 1);
    }

    /**
     * <p>Getter for the field <code>year</code>.</p>
     *
     * @return a int.
     */
    public int getYear() {
        return year;
    }

    /**
     * <p>Setter for the field <code>year</code>.</p>
     *
     * @param year a int.
     */
    public void setYear(int year) {
        this.year = year;
    }

    /**
     * <p>Getter for the field <code>month</code>.</p>
     *
     * @return a int.
     */
    public int getMonth() {
        return month;
    }

    /**
     * <p>Setter for the field <code>month</code>.</p>
     *
     * @param month a int.
     */
    public void setMonth(int month) {
        this.month = month;
    }

    /**
     * <p>Getter for the field <code>day</code>.</p>
     *
     * @return a int.
     */
    public int getDay() {
        return day;
    }

    /**
     * <p>Setter for the field <code>day</code>.</p>
     *
     * @param day a int.
     */
    public void setDay(int day) {
        this.day = day;
    }


    /** {@inheritDoc} */
    @Override
    public String toString() {
        return "DateValue{" +
                "year=" + year +
                ", month=" + month +
                ", day=" + day +
                '}';
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof DateValue)) return false;

        DateValue dateValue = (DateValue) o;

        if (day != dateValue.day) return false;
        if (month != dateValue.month) return false;
        if (year != dateValue.year) return false;

        return true;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        int result = year;
        result = 31 * result + month;
        result = 31 * result + day;
        return result;
    }
}
