package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.model.expressions.Value
import javafx.beans.property.ReadOnlyStringProperty
import javafx.beans.property.SimpleStringProperty

/**
 * A cell which contains concrete values. The cells of a [ConcreteSpecification] are of this
 * class.
 *
 * @author Benjamin Alt
 */
data class ConcreteCell(val value: Value) : StringReadable {
    override val stringRepresentationProperty: ReadOnlyStringProperty = SimpleStringProperty()

    override fun toString(): String = value.toString()
}
