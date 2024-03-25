package edu.kit.iti.formal.stvs.model.config

import javafx.beans.property.DoubleProperty
import javafx.beans.property.SimpleDoubleProperty
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient
import tornadofx.getValue
import tornadofx.setValue

/**
 * Configuration for table column. Contains GUI-related information about a column.
 *
 * @author Philipp
 */
@Serializable
class ColumnConfig {
    @Transient
    private val widthProperty = SimpleDoubleProperty(100.0)
    var width by widthProperty

    /**
     * Create a new ColumnConfig.
     *
     * @param colwidth The initial column width
     */
    constructor(colwidth: Double=100.0) {
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
