/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
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