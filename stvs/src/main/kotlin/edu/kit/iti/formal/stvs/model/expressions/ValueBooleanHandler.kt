package edu.kit.iti.formal.stvs.model.expressions

/**
 * Gets invoked by [ValueBool.match]. This interface provides a way to handle a value with
 * unknown type by calling [Value.match]. If the value is an instance of [ValueBool]
 * this handler is invoked.
 */
fun interface ValueBooleanHandler<R> {
    /**
     * This method is called by [ValueBool.match].
     *
     * @param value The value that the matched value represents
     * @return Object of type `R`
     */
    fun handle(value: Boolean): R
}
