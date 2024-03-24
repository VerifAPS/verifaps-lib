package edu.kit.iti.formal.stvs.model.expressions

/**
 * Gets invoked by [TypeEnum.match]. This interface provides a way to handle an unknown type
 * by calling [Type.match]. If the type is an instance of [TypeEnum] this handler is
 * called.
 */
fun interface TypeEnumHandler<R> {
    /**
     * Must implement a method that gets called by [TypeEnum.match] and handle the enum type
     * accordingly.
     *
     * @param typeEnum [TypeEnum] from which this method was called
     * @return Object of type `R`
     */
    fun handle(typeEnum: TypeEnum?): R
}
