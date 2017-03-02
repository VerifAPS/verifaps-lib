package edu.kit.iti.formal.stvs.util;

import javafx.application.Platform;

/**
 * FIXME: write docs
 * Created by leonk on 08.02.2017.
 *
 * @author Leon Kaucher
 */
public class JavaFXAsyncTask<T> extends Thread {
  private final AsyncRunner<T> runner;
  private final AsyncTaskCompletedHandler<T> resultHandler;

  /**
   * <p>
   * Constructor for an asynchronous task.
   * </p>
   *
   * @param runner The portion of action to be run asynchronously (a functional interface).
   * @param resultHandler The portion of the action to be run synchronously with any other AsyncTasks.
   */
  public JavaFXAsyncTask(AsyncRunner<T> runner, AsyncTaskCompletedHandler<T> resultHandler) {
    super();
    this.runner = runner;
    this.resultHandler = resultHandler;
  }

  public void terminate() {
    this.interrupt();
  }

  @Override
  public void run() {
    try {
      T result = runner.run();
      Platform.runLater(() -> resultHandler.onSuccess(result));
    } catch (Exception exception) {
      Platform.runLater(() -> resultHandler.onException(exception));
    }
  }
}
