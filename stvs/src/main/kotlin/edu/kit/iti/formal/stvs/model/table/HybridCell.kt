package edu.kit.iti.formal.stvs.model.table

import javafx.beans.property.SimpleListProperty
import javafx.beans.property.SimpleStringProperty
import javafx.collections.FXCollections
import tornadofx.getValue
import tornadofx.setValue

/**
 *
 * The model for a cell (for
 * [edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableCell])
 * that both has an abstract cell model, a [CellOperationProvider] (that is, either a
 * [ConstraintCell] or [ConstraintDuration]), and a list of counterexample
 * strings that should be viewed in-place below these cells.
 *
 * @author Philipp
 */
class HybridCell<C : CellOperationProvider?>(val cell: C) : CellOperationProvider {
    val counterExamplesProperty = SimpleListProperty(FXCollections.observableArrayList<String>())
    var counterExamples by counterExamplesProperty

    override val commentProperty = SimpleStringProperty()
    override val stringRepresentationProperty = SimpleStringProperty()

    /**
     * Makes all counterexample cells disappear. After this call
     * <tt>[.counterExamplesProperty].isEmpty()</tt> is true.
     */
    fun clearCounterExample() {
        counterExamplesProperty.setAll()
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as HybridCell<*>

        if (asString != other.asString) return false
        if (comment != other.comment) return false
        if (counterExamples != other.counterExamples) return false

        return true
    }

    override fun hashCode(): Int {
        var result = asString.hashCode()
        result = 31 * result + comment.hashCode()
        result = 31 * result + counterExamples.hashCode()
        return result
    }

}
