package edu.kit.iti.formal.stvs.util;

import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Created by leonk on 08.02.2017.
 *
 * @author Leon Kaucher
 */
public class AsyncTask<T> extends Thread {
  private final AsyncRunner<T> runAsync;
  private final AsyncTaskCompletedHandler<T> runLater;
  private AtomicBoolean isRunning = new AtomicBoolean(false);

  /**
   * <p>Constructor for an asynchronous task.</p>
   *
   * @param runAsync The portion of action to be run
   *                 asynchronously (a functional interface).
   * @param runLater The portion of the action to be run synchronously with
   *                 any other AsyncTasks.
   */
  public AsyncTask(AsyncRunner<T> runAsync, AsyncTaskCompletedHandler<T> runLater) {
    super();
    this.runAsync = runAsync;
    this.runLater = runLater;
  }

  public void terminate() {
    isRunning.set(false);
  }

  public boolean isRunning() {
    return isRunning.get();
  }

  @Override
  public void run() {
    isRunning.set(true);
    T result = runAsync.run(isRunning);
    runLater.completedWith(result);
    isRunning.set(false);
  }
}
