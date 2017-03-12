package edu.kit.iti.formal.stvs.logic.verification;

import java.io.IOException;
import java.util.Optional;
import java.util.concurrent.TimeUnit;

import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import org.apache.commons.io.IOUtils;

/**
 * Detects when a process is finished and invokes the associated listeners. Adapted from
 * https://beradrian.wordpress.com/2008/11/03/detecting-process-exit-in-java/.
 *
 * @author Benjamin Alt
 */
public class ProcessMonitor extends Thread {

  /**
   * The process for which we have to detect the end.
   */
  private Process process;
  private BooleanProperty processFinished;
  private int timeout;
  private boolean aborted;
  private Exception error;

  /**
   * Starts the detection for the given process.
   *
   * @param process the process for which one would like to detect when it is finished
   * @param timeout Timeout after which the process is killed automatically
   */
  public ProcessMonitor(Process process, int timeout) {
    try {
      /* Test if the process is finished */
      process.exitValue();
      throw new IllegalArgumentException("The process has already finished.");
    } catch (IllegalThreadStateException exc) {
      this.process = process;
      this.processFinished = new SimpleBooleanProperty(false);
      this.timeout = timeout;
    }
  }

  public Process getProcess() {
    return process;
  }

  public Optional<Exception> getError() {
    return Optional.ofNullable(error);
  }

  /**
   * runs an external process and wait until {@code timeout} or until it is interrupted.
   */
  public void run() {
    aborted = false;
    try {
      // wait for the process to finish
      if (!process.waitFor(timeout, TimeUnit.SECONDS)) {
        process.destroy();
        aborted = true;
      }
      if (process.exitValue() != 0) {
        error = new IOException("Process ended with error " + process.exitValue()
            + " and error output:\n" + IOUtils.toString(process.getErrorStream(), "utf-8"));
      }
      processFinished.set(true);
    } catch (InterruptedException e) {
      // intentionally left empty. Process is destroyed somewhere else
    } catch (IOException e) {
      error = e;
      e.printStackTrace();
      processFinished.set(true);
    }
  }

  public boolean isProcessFinished() {
    return processFinished.get();
  }

  public BooleanProperty processFinishedProperty() {
    return processFinished;
  }

  public boolean isAborted() {
    return aborted;
  }
}
