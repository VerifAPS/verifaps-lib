package edu.kit.iti.formal.stvs.model.config

import javafx.beans.property.DoubleProperty
import javafx.beans.property.SimpleDoubleProperty

/**
 * Configuration for table column. Contains GUI-related information about a column.
 *
 * @author Philipp
 */
class ColumnConfig {
    private var width: DoubleProperty

    /**
     * Default ColumnConfig.
     */
    constructor() {
        width = SimpleDoubleProperty(100.0)
    }

    /**
     * Create a new ColumnConfig.
     *
     * @param colwidth The initial column width
     */
    constructor(colwidth: Double) {
        require(!(colwidth <= 0)) { "Column width must be positive" }
        width = SimpleDoubleProperty(colwidth)
    }

    /**
     * Get the current column width.
     *
     * @return The current column width
     */
    fun getWidth(): Double {
        return width.get()
    }

    /**
     * Set the current column width.
     *
     * @param width The current column width
     */
    fun setWidth(width: Double) {
        require(!(width <= 0)) { "Column width must be positive" }
        this.width.set(width)
    }

    override fun equals(obj: Any?): Boolean {
        if (this === obj) {
            return true
        }
        if (obj !is ColumnConfig) {
            return false
        }

        return width.get() == obj.width.get()
    }

    override fun hashCode(): Int {
        val bits = java.lang.Double.doubleToRawLongBits(width.get())
        return (bits xor (bits shr 32)).toInt()
    }

    fun widthProperty(): DoubleProperty {
        return width
    }
}
