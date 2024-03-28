package edu.kit.iti.formal.stvs.model.common

import kotlinx.serialization.Serializable

/**
 * A variable, having a name and a type.
 * @author Benjamin Alt
 */
@Serializable
sealed interface Variable : Named {
    val type: String
}
