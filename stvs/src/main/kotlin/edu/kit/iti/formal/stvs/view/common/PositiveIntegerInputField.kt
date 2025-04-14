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

    fun isValid(): Boolean {
        return valid.get()
    }

    fun validProperty(): BooleanProperty {
        return valid
    }
}
