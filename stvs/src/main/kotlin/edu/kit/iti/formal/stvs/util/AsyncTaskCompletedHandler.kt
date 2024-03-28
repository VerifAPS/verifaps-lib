package edu.kit.iti.formal.stvs.util

/**
 * This interface represents a handler that gets called after a [JavaFxAsyncTask] has
 * completed its. work.
 */
interface AsyncTaskCompletedHandler<T> {
    fun onSuccess(computedValue: T)

    fun onException(exception: Exception?)
}
