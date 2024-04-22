package edu.kit.iti.formal.stvs.model.table

/**
 * Interface for classes that Provide commonly needed functionality for editing, like having a
 * string property and being commentable.
 * @author Benjamin Alt
 */
interface CellOperationProvider : Commentable, StringEditable {
    /**
     * Prints a minimal string including the string representation and optionally adds the comment, if
     * not null.
     * (should only used for debugging purposes, i.e. in toString methods)
     * @return a minimal string
     */
    fun debuggingString() = asString + (comment?.let { " (comment: \"$it\")" } ?: "")
}
