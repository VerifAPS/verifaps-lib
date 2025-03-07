package edu.kit.iti.formal.stvs.model.expressions

/**
 * Gets invoked by [ValueEnum.match]. This interface provides a way to handle a value of
 * unknown type by calling [Value.match]. If the value is an instance of [ValueEnum]
 * this handler is called.
 */
fun interface ValueEnumHandler<R> {
    /**
     * Must implement a method that gets called by [ValueEnum.match].
     *
     * @param value The value that the matched value represents
     * @return Object of type `R`
     */
    fun handle(value: ValueEnum): R
}
