package edu.kit.iti.formal.stvs.model.config

import javafx.beans.property.SimpleDoubleProperty

/**
 * Configuration for table column. Contains GUI-related information about a column.
 *
 * @author Philipp
 */
class ColumnConfig {
    private val widthProperty = SimpleDoubleProperty(100.0)
    var width: Double
        get() = widthProperty.get()
        set(value) {
            require(value >= 0)
            widthProperty.set(value)
        }

    /**
     * Create a new ColumnConfig.
     *
     * @param colwidth The initial column width
     */
    constructor(colwidth: Double = 100.0) {
        require(!(colwidth <= 0)) { "Column width must be positive" }
        width = colwidth
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ColumnConfig) return false

        if (width != other.width) return false

        return true
    }

    override fun hashCode(): Int {
        return width.hashCode()
    }


}
