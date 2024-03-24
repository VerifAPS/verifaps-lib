package edu.kit.iti.formal.stvs.model.expressions

import java.util.*

/**
 * The super-interface for all Types.
 *
 * @author Philipp
 */
sealed interface Type {
    /**
     * matches the actual type present. Subclasses call the correct function.
     *
     * @param matchIntType in case its a [TypeInt]
     * @param matchBoolType in case its a [TypeBool]
     * @param matchEnumType in case its a [TypeEnum]
     * @param <R> the return type of the visitor
     * @return the return value of the visitor
    </R> */
    fun <R> match(
        matchIntType: TypeIntegerHandler<R>, matchBoolType: TypeBooleanHandler<R>,
        matchEnumType: TypeEnumHandler<R>
    ): R?

    /**
     * Finds out whether this type checks against another type, which means any value of this type can
     * be used as a value of the other type.
     * This mostly means type equality or a supertype relation.
     *
     * @param other the other type ot subsume.
     * @return whether it does subsume the other type or not.
     */
    fun checksAgainst(other: Type): Boolean

    /**
     * Get the type name of this type in a human-readable format (in contrast to this classes'
     * toString()). This can be used to show the type in a GUI, for example.
     *
     * @return a string that should match the type name as it is usually used in st-code.
     */
    val typeName: String

    /**
     * Parse a literal of this type to a value. Can be used for parsing user-input into TextFields
     * when the type is known, for example.
     *
     * @param literal the literal string to parse
     * @return optionally a resulting value
     */
    fun parseLiteral(literal: String): Optional<Value>

    /**
     * For any <tt>[Type] type</tt> the following must be true:
     * <tt>type.generateDefaultValue().getErrorType().checksAgainst(type)</tt>
     *
     * @return a default value of this given type.
     */
    fun generateDefaultValue(): Value
}
