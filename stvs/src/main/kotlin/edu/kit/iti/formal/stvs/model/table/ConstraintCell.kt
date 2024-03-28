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
    override val stringRepresentationProperty: StringProperty = SimpleStringProperty()
    override val commentProperty: StringProperty = SimpleStringProperty()

    constructor(constraintCell: ConstraintCell?) : this(constraintCell!!.asString) {
        comment = constraintCell.comment
    }

    override fun toString(): String {
        return debuggingString()!!
    }
}
