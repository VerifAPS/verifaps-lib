package edu.kit.iti.formal.automation.datatypes.values

data class DateAndTimeData(var date: DateData = DateData(),
                           var tod: TimeofDayData = TimeofDayData()) {
    var hours: Int
        get() = tod.hours
        set(hours) {
            tod.hours = hours
        }

    var minutes: Int
        get() = tod.minutes
        set(minutes) {
            tod.minutes = minutes
        }

    var seconds: Int
        get() = tod.seconds
        set(seconds) {
            tod.seconds = seconds
        }

    var year: Int
        get() = date.year
        set(year) {
            date.year = year
        }

    var day: Int
        get() = date.day
        set(day) {
            date.day = day
        }

    var month: Int
        get() = date.month
        set(month) {
            date.month = month
        }

    var millieSeconds: Int
        get() = tod.millieseconds
        set(ms) {
            tod.millieseconds = ms
        }

    constructor(years: Int, months: Int, days: Int, hours: Int, minutes: Int, seconds: Int)
            : this(DateData(years, months, days), TimeofDayData(hours, minutes, seconds))
}
