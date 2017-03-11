package edu.kit.iti.formal.stvs.util;

import java.util.Timer;
import java.util.TimerTask;

import javafx.application.Platform;

/**
 * A Thread that executes an {@link AsyncRunner} and calls a {@link AsyncTaskCompletedHandler} after
 * completion. The handler is always called within the JavaFX main thread.
 *
 * @author Leon Kaucher
 */
public class JavaFxAsyncTask<T> extends Thread {
  private final AsyncRunner<T> runner;
  private final AsyncTaskCompletedHandler<T> resultHandler;
  private final Timer processTerminatorTask;

  /**
   * Constructor for an asynchronous task.
   *
   * @param timeout time before the runner will be terminated
   * @param runner The portion of action to be run asynchronously (a functional interface).
   * @param resultHandler The portion of the action to be run synchronously (in javafx's EDT) with
   *        any other AsyncTasks.
   */
  public JavaFxAsyncTask(int timeout, AsyncRunner<T> runner,
                         AsyncTaskCompletedHandler<T> resultHandler) {
    super();
    setDaemon(true);
    this.runner = runner;
    this.resultHandler = resultHandler;
    this.processTerminatorTask = new Timer();
    processTerminatorTask.schedule(new TimerTask() {
      @Override
      public void run() {
        terminate();
      }
    }, timeout * 1000);

  }

  /**
   * Interrupts this thread and terminates the process that the runner is depending on.
   */
  public void terminate() {
    processTerminatorTask.cancel();
    this.interrupt();
    runner.terminate();
  }

  @Override
  public void run() {
    try {
      T result = runner.run();
      Platform.runLater(() -> resultHandler.onSuccess(result));
    } catch (Exception exception) {
      Platform.runLater(() -> resultHandler.onException(exception));
    } finally {
      processTerminatorTask.cancel();
    }
  }
}
