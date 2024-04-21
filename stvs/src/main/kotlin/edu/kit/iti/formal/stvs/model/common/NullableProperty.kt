package edu.kit.iti.formal.stvs.model.common

import javafx.beans.property.SimpleObjectProperty

/**
 * A property the value of which may be null.
 *
 * @author Lukas Fritsch
 */
class NullableProperty<T> : SimpleObjectProperty<T> {
    /**
     * Create a new NullableProperty from an initial value.
     * @param initial The initial value
     */
    constructor(initial: T) : super(initial)

    /**
     * Create a new NullableProperty with an empty initial value; the value of the property is set
     * to null.
     */
    constructor() : super(null)
}
