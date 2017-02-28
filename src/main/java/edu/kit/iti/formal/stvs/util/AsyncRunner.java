package edu.kit.iti.formal.stvs.util;

import java.util.concurrent.atomic.AtomicBoolean;

/**
 * This interface represents the action that should be executed
 * while a {@link AsyncTask} is running.
 */
@FunctionalInterface
public interface AsyncRunner<T> {
  /**
   * This method must be implemented to define what the {@link AsyncTask} is doing while running.
   * Whatever is done in this method must check {@code isRunning} periodically to react if the task
   * should be stopped.
   *
   * @param isRunning indicator if the {@link AsyncTask} should keep running.
   * @return Object of type {@code T} that is computed by this method
   */
  T run(AtomicBoolean isRunning);
}
