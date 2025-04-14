package edu.kit.iti.formal.stvs.model.expressions

/**
 * Helper class for quickly creating values of [TypeEnum].
 *
 * @author Philipp
 */
object TypeFactory {
    /**
     * Generates an enum type from name and values.
     *
     * @param name the name of the enum type
     * @param values the possible values that this enum type has
     * @return an instance of [TypeEnum]
     */
    @JvmStatic
    fun enumOfName(name: String, vararg values: String): TypeEnum {
        return TypeEnum(name, listOf(*values))
    }
}
