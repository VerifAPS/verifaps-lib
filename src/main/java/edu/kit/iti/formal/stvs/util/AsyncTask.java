package edu.kit.iti.formal.stvs.util;

import javafx.application.Platform;

import java.util.function.Consumer;
import java.util.function.Supplier;

/**
 * Created by leonk on 08.02.2017.
 */
public class AsyncTask<T> extends Thread{
  private final Supplier<T> runAsnc;
  private final Consumer<T> runOnPlatform;

  public AsyncTask(Supplier<T> runAsnc, Consumer<T> runOnPlatform){
    super();
    this.runAsnc = runAsnc;
    this.runOnPlatform = runOnPlatform;
  }

  @Override
  public void run(){
    T result = runAsnc.get();
    Platform.runLater(() -> runOnPlatform.accept(result));
  }
}
