package edu.kit.iti.formal.stvs.util;

import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Created by leonk on 08.02.2017.
 *
 * @author Leon Kaucher
 */
public class AsyncTask<T> extends Thread {
  private final AsyncRunner<T> runAsnc;
  private final AsyncTaskCompletedHandler<T> runLater;
  private AtomicBoolean isRunning = new AtomicBoolean(false);

  public AsyncTask(AsyncRunner<T> runAsnc, AsyncTaskCompletedHandler<T> runLater) {
    super();
    this.runAsnc = runAsnc;
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
    T result = runAsnc.run(isRunning);
    runLater.completedWith(result);
    isRunning.set(false);
  }
}
