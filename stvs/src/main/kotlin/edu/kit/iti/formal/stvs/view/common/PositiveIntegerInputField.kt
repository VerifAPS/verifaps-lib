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
package edu.kit.iti.formal.stvs.view.common

import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.beans.property.BooleanProperty
import javafx.beans.property.SimpleBooleanProperty
import javafx.geometry.Pos
import javafx.scene.control.TextField

/**
 * A Input field that only allows positive integers.
 *
 * @author Carsten Csiky
 */
class PositiveIntegerInputField : TextField() {
    private val valid: BooleanProperty

    /**
     * Creates an instances of this positive integer only field.
     */
    init {
        textProperty().addListener { observableValue, old, newValue ->
            this.onInputChange(newValue)
        }
        valid = SimpleBooleanProperty()
        valid.addListener { _, _, value: Boolean ->
            this.onValidStateChange(value)
        }
        alignmentProperty().value = Pos.CENTER_RIGHT
        ViewUtils.setupClass(this)
    }

    private fun onValidStateChange(value: Boolean) {
        if (value) {
            styleClass.add("valid")
        } else {
            styleClass.remove("valid")
        }
    }

    private fun onInputChange(newValue: String) {
        valid.set(text.trim { it <= ' ' }.matches("(?!0)[0-9]+".toRegex()))
    }

    val integer: Int?
        /**
         * get inputfield value as an integer if no integer representation is available Optional.empty()
         * will be returned
         *
         * @return value as an integer
         */
        get() = if (valid.get()) {
            text.trim { it <= ' ' }.toInt()
        } else {
            null
        }

    fun isValid(): Boolean = valid.get()

    fun validProperty(): BooleanProperty = valid
}