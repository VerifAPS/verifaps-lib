package edu.kit.iti.formal.stvs.view.spec

import javafx.beans.property.BooleanProperty

/**
 * Created by leonk on 11.01.2017.
 *
 * @author Leon Kaucher
 */
interface Lockable {
    var editable: Boolean
        get() = editableProperty.get()
        set(value) = editableProperty.set(value)

    val editableProperty: BooleanProperty
}
