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
 * <p>TimeOfDayValue class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class TimeOfDayValue {
    private int hours, minutes, seconds, millieseconds;

    /**
     * <p>Constructor for TimeOfDayValue.</p>
     *
     * @param hours a int.
     * @param minutes a int.
     * @param seconds a int.
     */
    public TimeOfDayValue(int hours, int minutes, int seconds) {
        this.hours = hours;
        this.minutes = minutes;
        this.seconds = seconds;
    }

    /**
     * <p>Constructor for TimeOfDayValue.</p>
     *
     * @param hour a int.
     * @param min a int.
     * @param sec a int.
     * @param ms a int.
     */
    public TimeOfDayValue(int hour, int min, int sec, int ms) {
        this(hour, min, sec);
        millieseconds = ms;
    }

    /**
     * <p>Constructor for TimeOfDayValue.</p>
     */
    public TimeOfDayValue() {
        this(0, 0, 0, 0);
    }

    /**
     * <p>Getter for the field <code>hours</code>.</p>
     *
     * @return a int.
     */
    public int getHours() {
        return hours;
    }

    /**
     * <p>Setter for the field <code>hours</code>.</p>
     *
     * @param hours a int.
     */
    public void setHours(int hours) {
        this.hours = hours;
    }

    /**
     * <p>Getter for the field <code>minutes</code>.</p>
     *
     * @return a int.
     */
    public int getMinutes() {
        return minutes;
    }

    /**
     * <p>Setter for the field <code>minutes</code>.</p>
     *
     * @param minutes a int.
     */
    public void setMinutes(int minutes) {
        this.minutes = minutes;
    }

    /**
     * <p>Getter for the field <code>seconds</code>.</p>
     *
     * @return a int.
     */
    public int getSeconds() {
        return seconds;
    }

    /**
     * <p>Setter for the field <code>seconds</code>.</p>
     *
     * @param seconds a int.
     */
    public void setSeconds(int seconds) {
        this.seconds = seconds;
    }

    /**
     * <p>Getter for the field <code>millieseconds</code>.</p>
     *
     * @return a int.
     */
    public int getMillieseconds() {
        return millieseconds;
    }

    /**
     * <p>Setter for the field <code>millieseconds</code>.</p>
     *
     * @param millieseconds a int.
     */
    public void setMillieseconds(int millieseconds) {
        this.millieseconds = millieseconds;
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof TimeOfDayValue)) return false;

        TimeOfDayValue that = (TimeOfDayValue) o;

        if (hours != that.hours) return false;
        if (millieseconds != that.millieseconds) return false;
        if (minutes != that.minutes) return false;
        if (seconds != that.seconds) return false;

        return true;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        int result = hours;
        result = 31 * result + minutes;
        result = 31 * result + seconds;
        result = 31 * result + millieseconds;
        return result;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return "TimeOfDayValue{" +
                "hours=" + hours +
                ", minutes=" + minutes +
                ", seconds=" + seconds +
                ", millieseconds=" + millieseconds +
                '}';
    }


}
