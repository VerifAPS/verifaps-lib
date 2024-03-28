package edu.kit.iti.formal.stvs.model.table

import javafx.beans.property.StringProperty

/**
 *
 *
 * The interface for anything that has a [StringProperty] with the intent of being used as a
 * comment (for example tables ([SpecificationTable]), cells ([ConstraintCell]) or rows
 * ([SpecificationRow])).
 *
 *
 * @author Benjamin Alt
 */
interface Commentable {
    var comment: String?
        get() = commentProperty.value
        set(value) = commentProperty.set(value)

    val commentProperty: StringProperty
}
