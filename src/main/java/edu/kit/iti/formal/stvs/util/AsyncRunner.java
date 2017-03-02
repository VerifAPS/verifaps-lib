package edu.kit.iti.formal.stvs.util;

/**
 * This interface represents the action that should be executed while a {@link JavaFxAsyncTask} is
 * running.
 */
@FunctionalInterface
public interface AsyncRunner<T> {
  /**
   * FIXME: Update Docs!
   * This method must be implemented to define what the {@link JavaFxAsyncTask} is doing while running.
   * Whatever is done in this method must check {@code isRunning} periodically to react if the task
   * should be stopped.
   *
   * @param isRunning indicator if the {@link JavaFxAsyncTask} should keep running.
   * @return Object of type {@code T} that is computed by this method
   */
  T run() throws Exception;

}
