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
}
