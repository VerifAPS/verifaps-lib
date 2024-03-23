package edu.kit.iti.formal.stvs.util;

/**
 * Created by leonk on 23.02.2017.
 */
@FunctionalInterface
public interface ThrowableHandler {
  public void handleThrowable(Throwable t);
}
