package edu.kit.iti.formal.stvs.util;

/**
 * This interface represents a handler that gets called after a {@link AsyncTask} has completed its
 * work.
 */
@FunctionalInterface
public interface AsyncTaskCompletedHandler<T> {
  /**
   * Must handle the result of the ended task. This gets called even if the task was stopped before
   * completion.
   *
   * @param data Object of type {@code T}
   */
  void completedWith(T data);
}
