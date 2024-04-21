package edu.kit.iti.formal.stvs.model.expressions

/**
 * Gets invoked by [TypeInt.match]. This interface provides a way to handle an unknown type by
 * calling [Type.match]. If the type is an instance of [TypeInt] this handler is called.
 */
fun interface TypeIntegerHandler<R> {
    /**
     * Must implement a method that gets called by [TypeInt.match].
     *
     * @return Object of type `R`
     */
    fun handle(): R
}
