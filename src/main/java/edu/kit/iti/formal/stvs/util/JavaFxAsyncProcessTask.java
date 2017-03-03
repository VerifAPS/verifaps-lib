package edu.kit.iti.formal.stvs.util;

import javafx.application.Platform;

import java.util.Timer;
import java.util.TimerTask;

/**
 * FIXME: write docs
 * Created by leonk on 08.02.2017.
 *
 * @author Leon Kaucher
 */
public class JavaFxAsyncProcessTask<T> extends Thread {
  private final AsyncRunner<T> runner;
  private final AsyncTaskCompletedHandler<T> resultHandler;
  private final Timer processTerminatorTask;

  /**
   * <p>
   * Constructor for an asynchronous task.
   * </p>
   *
   * @param runner The portion of action to be run asynchronously (a functional interface).
   * @param resultHandler The portion of the action to be run synchronously (in javafx's EDT)
   *                      with any other AsyncTasks.
   */
  public JavaFxAsyncProcessTask(int timeout, AsyncRunner<T> runner, AsyncTaskCompletedHandler<T> resultHandler) {
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

  public void terminate() {
    processTerminatorTask.cancel();
    this.interrupt();
    Process runningProcess = runner.getProcess();
    if (runningProcess != null && runningProcess.isAlive()) {
      runningProcess.destroy();
    }
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
