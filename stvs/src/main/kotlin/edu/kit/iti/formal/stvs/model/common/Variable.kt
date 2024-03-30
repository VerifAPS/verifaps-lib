package edu.kit.iti.formal.stvs.model.common

/**
 * A variable, having a name and a type.
 * @author Benjamin Alt
 */
sealed interface Variable : Named {
    val type: String
}
