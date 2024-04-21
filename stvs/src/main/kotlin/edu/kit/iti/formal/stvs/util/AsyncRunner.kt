package edu.kit.iti.formal.stvs.util

/**
 * This interface represents the action that should be executed while a
 * [JavaFxAsyncTask] is running an that depends on a process.
 */
interface AsyncRunner<T> {
    /**
     * This method must be implemented to define what the [JavaFxAsyncTask] is doing
     * while running.
     *
     * @return Object of type `T` that is computed by this method
     * @throws Exception exception while running
     */
    @Throws(Exception::class)
    fun run(): T

    fun terminate()
}
