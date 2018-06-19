package edu.kit.iti.formal.automation.datatypes.values

import edu.kit.iti.formal.automation.sfclang.split

data class DateData(var year: Int = 0,
                    var month: Int = 0,
                    var day: Int = 0) {
    companion object {
        fun parse(str: String): DateData {
            val pattern = Regex("(?<year>\\d\\d\\d\\d)-(?<month>\\d?\\d)-(?<day>\\d?\\d)")
            val (_, _, value) = split(str)
            val matcher = pattern.matchEntire(value)
                    ?: throw IllegalArgumentException("given string isType not a time of day value")
            val (_,year, month, day) = matcher.groupValues
            return DateData(year.toInt(), month.toInt(), day.toInt())
        }
    }
}
