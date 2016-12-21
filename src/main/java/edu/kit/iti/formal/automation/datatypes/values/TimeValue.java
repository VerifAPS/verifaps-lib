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
 * Created by weigl on 11.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class TimeValue {
    private double days, hours, minutes, seconds, millieseconds;

    /**
     * <p>Constructor for TimeValue.</p>
     */
    public TimeValue() {

    }

    /**
     * <p>Constructor for TimeValue.</p>
     *
     * @param days a double.
     * @param hours a double.
     * @param minutes a double.
     * @param seconds a double.
     * @param millieseconds a double.
     */
    public TimeValue(double days, double hours, double minutes, double seconds, double millieseconds) {
        this.days = days;
        this.hours = hours;
        this.minutes = minutes;
        this.seconds = seconds;
        this.millieseconds = millieseconds;
    }

    /**
     * <p>asLong.</p>
     *
     * @return a long.
     */
    public long asLong() {
        return (long) (((((days * 24) + hours) * 60 + minutes) * 60 + seconds) * 1000 + millieseconds);
    }

    /**
     * <p>Getter for the field <code>days</code>.</p>
     *
     * @return a double.
     */
    public double getDays() {
        return days;
    }

    /**
     * <p>Setter for the field <code>days</code>.</p>
     *
     * @param days a double.
     */
    public void setDays(double days) {
        this.days = days;
    }

    /**
     * <p>Getter for the field <code>hours</code>.</p>
     *
     * @return a double.
     */
    public double getHours() {
        return hours;
    }

    /**
     * <p>Setter for the field <code>hours</code>.</p>
     *
     * @param hours a double.
     */
    public void setHours(double hours) {
        this.hours = hours;
    }

    /**
     * <p>Getter for the field <code>minutes</code>.</p>
     *
     * @return a double.
     */
    public double getMinutes() {
        return minutes;
    }

    /**
     * <p>Setter for the field <code>minutes</code>.</p>
     *
     * @param minutes a double.
     */
    public void setMinutes(double minutes) {
        this.minutes = minutes;
    }

    /**
     * <p>Getter for the field <code>seconds</code>.</p>
     *
     * @return a double.
     */
    public double getSeconds() {
        return seconds;
    }

    /**
     * <p>Setter for the field <code>seconds</code>.</p>
     *
     * @param seconds a double.
     */
    public void setSeconds(double seconds) {
        this.seconds = seconds;
    }

    /**
     * <p>Getter for the field <code>millieseconds</code>.</p>
     *
     * @return a double.
     */
    public double getMillieseconds() {
        return millieseconds;
    }

    /**
     * <p>Setter for the field <code>millieseconds</code>.</p>
     *
     * @param millieseconds a double.
     */
    public void setMillieseconds(double millieseconds) {
        this.millieseconds = millieseconds;
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof TimeValue)) return false;

        TimeValue timeValue = (TimeValue) o;

        if (Double.compare(timeValue.days, days) != 0) return false;
        if (Double.compare(timeValue.hours, hours) != 0) return false;
        if (Double.compare(timeValue.millieseconds, millieseconds) != 0) return false;
        if (Double.compare(timeValue.minutes, minutes) != 0) return false;
        if (Double.compare(timeValue.seconds, seconds) != 0) return false;

        return true;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        int result;
        long temp;
        temp = Double.doubleToLongBits(days);
        result = (int) (temp ^ (temp >>> 32));
        temp = Double.doubleToLongBits(hours);
        result = 31 * result + (int) (temp ^ (temp >>> 32));
        temp = Double.doubleToLongBits(minutes);
        result = 31 * result + (int) (temp ^ (temp >>> 32));
        temp = Double.doubleToLongBits(seconds);
        result = 31 * result + (int) (temp ^ (temp >>> 32));
        temp = Double.doubleToLongBits(millieseconds);
        result = 31 * result + (int) (temp ^ (temp >>> 32));
        return result;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return "TimeValue{" +
                "days=" + days +
                ", hours=" + hours +
                ", minutes=" + minutes +
                ", seconds=" + seconds +
                ", millieseconds=" + millieseconds +
                '}';
    }

    /**
     * <p>asMillieseconds.</p>
     *
     * @return a long.
     */
    public long asMillieseconds() {
        return asLong();
    }
}
