package edu.kit.iti.formal.automation.datatypes.values;

public class TimeOfDayValue {
    private int hours, minutes, seconds, millieseconds;

    public TimeOfDayValue(int hours, int minutes, int seconds) {
        this.hours = hours;
        this.minutes = minutes;
        this.seconds = seconds;
    }

    public TimeOfDayValue(int hour, int min, int sec, int ms) {
        this(hour, min, sec);
        millieseconds = ms;
    }

    public TimeOfDayValue() {
        this(0, 0, 0, 0);
    }

    public int getHours() {
        return hours;
    }

    public void setHours(int hours) {
        this.hours = hours;
    }

    public int getMinutes() {
        return minutes;
    }

    public void setMinutes(int minutes) {
        this.minutes = minutes;
    }

    public int getSeconds() {
        return seconds;
    }

    public void setSeconds(int seconds) {
        this.seconds = seconds;
    }

    public int getMillieseconds() {
        return millieseconds;
    }

    public void setMillieseconds(int millieseconds) {
        this.millieseconds = millieseconds;
    }

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

    @Override
    public int hashCode() {
        int result = hours;
        result = 31 * result + minutes;
        result = 31 * result + seconds;
        result = 31 * result + millieseconds;
        return result;
    }

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
