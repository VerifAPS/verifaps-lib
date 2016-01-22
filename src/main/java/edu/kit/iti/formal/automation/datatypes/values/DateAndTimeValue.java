package edu.kit.iti.formal.automation.datatypes.values;

public class DateAndTimeValue {
    private DateValue date = new DateValue();
    private TimeOfDayValue tod = new TimeOfDayValue();

    public DateAndTimeValue(DateValue date, TimeOfDayValue tod) {
        this.date = date;
        this.tod = tod;
    }

    public DateAndTimeValue(int years, int months, int days, int hours, int minutes, int seconds) {
        setYear(years);
        setMonth(months);
        setDay(days);
        setHours(hours);
        setMinutes(minutes);
        setSeconds(seconds);
    }

    @Override
    public String toString() {
        return "DateAndTimeValue{" +
                "date=" + date +
                ", tod=" + tod +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof DateAndTimeValue)) return false;

        DateAndTimeValue that = (DateAndTimeValue) o;

        if (!date.equals(that.date)) return false;
        if (!tod.equals(that.tod)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = date.hashCode();
        result = 31 * result + tod.hashCode();
        return result;
    }

    public DateValue getDate() {
        return date;
    }

    public void setDate(DateValue date) {
        this.date = date;
    }

    public TimeOfDayValue getTod() {
        return tod;
    }

    public void setTod(TimeOfDayValue tod) {
        this.tod = tod;
    }

    public void setSeconds(int seconds) {
        tod.setSeconds(seconds);
    }

    public int getHours() {
        return tod.getHours();
    }

    public void setHours(int hours) {
        tod.setHours(hours);
    }

    public int getMinutes() {
        return tod.getMinutes();
    }

    public void setMinutes(int minutes) {
        tod.setMinutes(minutes);
    }

    public int getSeconds() {
        return tod.getSeconds();
    }

    public int getYear() {
        return date.getYear();
    }

    public void setDay(int day) {
        date.setDay(day);
    }

    public void setMonth(int month) {
        date.setMonth(month);
    }

    public void setYear(int year) {
        date.setYear(year);
    }

    public int getDay() {
        return date.getDay();
    }

    public int getMonth() {
        return date.getMonth();
    }

    public int getMillieSeconds() {
        return tod.getMillieseconds();
    }
}