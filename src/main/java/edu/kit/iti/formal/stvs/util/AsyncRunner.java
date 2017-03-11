package edu.kit.iti.formal.stvs.util;

/**
 * This interface represents the action that should be executed while a
 * {@link JavaFxAsyncProcessTask} is running an that depends on a process.
 */
public interface AsyncRunner<T> {
  /**
   * This method must be implemented to define what the {@link JavaFxAsyncProcessTask} is doing
   * while running.
   *
   * @return Object of type {@code T} that is computed by this method
   */
  T run() throws Exception;

  void terminate();

}
