package edu.kit.iti.formal.stvs.model.table

import javafx.beans.property.SimpleStringProperty
import javafx.beans.property.StringProperty

/**
 * A cell containing constraint expression (for the syntax, see
 * https://git.scc.kit.edu/peese/stverificationstudio/issues/25). The cells in a
 * [ConstraintSpecification] are of this type.
 *
 * @author Benjamin Alt
 */
class ConstraintCell(stringRepresentation: String?) : CellOperationProvider {
    override val stringRepresentationProperty: StringProperty = SimpleStringProperty(stringRepresentation)
    override val commentProperty: StringProperty = SimpleStringProperty()

    constructor(constraintCell: ConstraintCell?) : this(constraintCell!!.asString) {
        comment = constraintCell.comment
    }

    override fun toString() = debuggingString()

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as ConstraintCell

        if (asString != other.asString) return false
        if (comment != other.comment) return false

        return true
    }

    override fun hashCode(): Int {
        var result = asString.hashCode()
        result = 31 * result + comment.hashCode()
        return result
    }


}
