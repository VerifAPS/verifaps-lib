package edu.kit.iti.formal.stvs.model.table

import javafx.beans.property.ReadOnlyStringProperty

/**
 * This interface is implemented by all classes having a string representation that can be read.
 *
 * @author Benjamin Alt
 */
interface StringReadable {
    val stringRepresentationProperty: ReadOnlyStringProperty
    val asString: String?
        get() = stringRepresentationProperty.get()
}
