package edu.kit.iti.formal.automation.datatypes.values;

public class DateValue {
    private int year, month, day;

    public DateValue(int year, int month, int day) {
        this.year = year;
        this.month = month;
        this.day = day;
    }

    public DateValue() {
        this(0, 1, 1);
    }

    public int getYear() {
        return year;
    }

    public void setYear(int year) {
        this.year = year;
    }

    public int getMonth() {
        return month;
    }

    public void setMonth(int month) {
        this.month = month;
    }

    public int getDay() {
        return day;
    }

    public void setDay(int day) {
        this.day = day;
    }


    @Override
    public String toString() {
        return "DateValue{" +
                "year=" + year +
                ", month=" + month +
                ", day=" + day +
                '}';
    }

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

    @Override
    public int hashCode() {
        int result = year;
        result = 31 * result + month;
        result = 31 * result + day;
        return result;
    }
}