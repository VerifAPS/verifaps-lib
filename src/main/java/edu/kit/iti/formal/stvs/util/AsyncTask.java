package edu.kit.iti.formal.stvs.util;

import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * Created by leonk on 08.02.2017.
 * @author Leon Kaucher
 */
public class AsyncTask<T> extends Thread {
  private final Function<AtomicBoolean, T> runAsnc;
  private final Consumer<T> runLater;
  private AtomicBoolean isRunning = new AtomicBoolean(false);

  public AsyncTask(Function<AtomicBoolean, T> runAsnc, Consumer<T> runLater) {
    super();
    this.runAsnc = runAsnc;
    this.runLater = runLater;
  }

  public void terminate() {
    isRunning.set(false);
  }

  public boolean isRunning(){
    return isRunning.get();
  }

  @Override
  public void run() {
    isRunning.set(true);
    T result = runAsnc.apply(isRunning);
    runLater.accept(result);
    isRunning.set(false);
  }
}
