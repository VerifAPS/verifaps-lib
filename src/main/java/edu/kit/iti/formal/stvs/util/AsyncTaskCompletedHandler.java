package edu.kit.iti.formal.stvs.util;

/**
 * This interface represents a handler that gets called after a {@link JavaFxAsyncTask} has completed its
 * work.
 */
public interface AsyncTaskCompletedHandler<T> {
  void onSuccess(T computedValue);

  void onException(Exception exception);
}
