package edu.kit.iti.formal.stvs.model.table

import javafx.beans.property.SimpleStringProperty
import javafx.beans.property.StringProperty

/**
 * An abstract duration given by a constraint rather than a concrete value. For the grammar of
 * constraint durations, see https://git.scc.kit.edu/peese/stverificationstudio/issues/25.
 *
 * @author Benjamin Alt
 */
class ConstraintDuration(stringRepresentation: String?) : CellOperationProvider {
    override val stringRepresentationProperty: StringProperty = SimpleStringProperty(stringRepresentation)
    override val commentProperty: StringProperty = SimpleStringProperty()

    constructor(sourceDuration: ConstraintDuration) : this(sourceDuration.asString) {
        comment = sourceDuration.comment
    }

    override fun toString(): String {
        return debuggingString()!!
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as ConstraintDuration

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
