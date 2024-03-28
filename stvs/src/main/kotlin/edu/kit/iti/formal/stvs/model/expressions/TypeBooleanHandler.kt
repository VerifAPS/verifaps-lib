package edu.kit.iti.formal.stvs.model.expressions

/**
 * Gets invoked by [TypeBool.match]. This interface provides a way to handle an unknown type
 * by calling [Type.match]. If the type is an instance of [TypeBool] this handler is
 * called.
 */
fun interface TypeBooleanHandler<R> {
    /**
     * Must implement a method that gets called by [TypeBool.match].
     *
     * @return Object of type `R`
     */
    fun handle(): R
}
