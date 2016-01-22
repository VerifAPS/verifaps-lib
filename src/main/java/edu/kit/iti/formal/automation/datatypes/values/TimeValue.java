package edu.kit.iti.formal.automation.datatypes.values;

/**
 * Created by weigl on 11.06.14.
 */
public class TimeValue {
    private double days, hours, minutes, seconds, millieseconds;

    public TimeValue() {

    }

    public TimeValue(double days, double hours, double minutes, double seconds, double millieseconds) {
        this.days = days;
        this.hours = hours;
        this.minutes = minutes;
        this.seconds = seconds;
        this.millieseconds = millieseconds;
    }

    public long asLong() {
        return (long) (((((days * 24) + hours) * 60 + minutes) * 60 + seconds) * 1000 + millieseconds);
    }

    public double getDays() {
        return days;
    }

    public void setDays(double days) {
        this.days = days;
    }

    public double getHours() {
        return hours;
    }

    public void setHours(double hours) {
        this.hours = hours;
    }

    public double getMinutes() {
        return minutes;
    }

    public void setMinutes(double minutes) {
        this.minutes = minutes;
    }

    public double getSeconds() {
        return seconds;
    }

    public void setSeconds(double seconds) {
        this.seconds = seconds;
    }

    public double getMillieseconds() {
        return millieseconds;
    }

    public void setMillieseconds(double millieseconds) {
        this.millieseconds = millieseconds;
    }

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

    public long asMillieseconds() {
        return asLong();
    }
}
