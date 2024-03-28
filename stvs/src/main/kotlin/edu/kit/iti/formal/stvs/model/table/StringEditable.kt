package edu.kit.iti.formal.stvs.model.table

import javafx.beans.property.StringProperty

/**
 * This interface is implemented by all classes with a string representation that can be read and
 * changed.
 *
 * @author Benjamin Alt
 */
interface StringEditable : StringReadable {
    override val stringRepresentationProperty: StringProperty
    fun setFromString(input: String) = stringRepresentationProperty.set(input)
}
