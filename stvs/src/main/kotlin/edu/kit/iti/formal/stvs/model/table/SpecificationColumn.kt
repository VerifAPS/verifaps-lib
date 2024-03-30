package edu.kit.iti.formal.stvs.model.table

import javafx.beans.property.SimpleStringProperty

/**
 * A column in a specification (see [SpecificationTable]). The generic type parameter C is the
 * type of the cells.
 *
 * @author Benjamin Alt
 */
data class SpecificationColumn<C>(val cells: List<C>) : Commentable {
    override val commentProperty = SimpleStringProperty("")
    override fun toString(): String {
        return "SpecificationColumn(cells: $cells, comment: $comment)"
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as SpecificationColumn<*>

        if (cells != other.cells) return false
        if (comment != other.comment) return false

        return true
    }

    override fun hashCode(): Int {
        var result = cells.hashCode()
        result = 31 * result + comment.hashCode()
        return result
    }


}
