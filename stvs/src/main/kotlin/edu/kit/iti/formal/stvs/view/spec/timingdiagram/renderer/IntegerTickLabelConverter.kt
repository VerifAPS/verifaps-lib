package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer

import javafx.util.StringConverter

/**
 * Created by csicar on 12.06.17.
 * Converts between Numbers and Strings
 * This class is used for the TickLabels on a NumberAxis, that should display only Integers.
 *
 */
/*
  based on: based on: https://stackoverflow.com/questions/23841268/how-to-make-javafx-chart-numberaxis-only-show-integer-value-not-double
  this approach was taken instead of extending the ValueAxis, because the required functionality
  that has to be implemented for implementing ValueAxis is quite involved (deciding how many
  tick-marks should be displayed, given a certain height of the widget, etc.)
 */
class IntegerTickLabelConverter : StringConverter<Number>() {
    override fun toString(number: Number): String {
        if (number.toInt().toDouble() == number.toDouble()) {
            return "" + number.toInt()
        }
        return ""
    }

    override fun fromString(s: String): Number {
        val value: Number = s.toDouble()
        return value
    }
}
