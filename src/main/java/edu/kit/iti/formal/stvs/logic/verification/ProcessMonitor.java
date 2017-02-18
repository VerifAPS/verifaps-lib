package edu.kit.iti.formal.stvs.logic.verification;

/**
 * Adapted from https://beradrian.wordpress.com/2008/11/03/detecting-process-exit-in-java/.
 * @author Benjamin Alt
 */

import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;

import java.util.concurrent.TimeUnit;

/**
 * Detects when a process is finished and invokes the associated listeners.
 */
public class ProcessMonitor extends Thread {

  /** The process for which we have to detect the end. */
  private Process process;
  private BooleanProperty processFinished;
  private int timeout;
  private boolean aborted;

  /**
   * Starts the detection for the given process
   * @param process the process for which we have to detect when it is finished
   */
  public ProcessMonitor(Process process, int timeout) {
    try {
      // test if the process is finished
      process.exitValue();
      throw new IllegalArgumentException("The process has already finished");
    } catch (IllegalThreadStateException exc) {
      this.process = process;
      this.processFinished = new SimpleBooleanProperty(false);
      this.timeout = timeout;
    }
  }

  /** @return the process that it is watched by this detector. */
  public Process getProcess() {
    return process;
  }

  public void run() {
    aborted = false;
    try {
      // wait for the process to finish
      if (!process.waitFor(timeout, TimeUnit.SECONDS)) {
        process.destroy();
        System.out.println("Aborted");
        aborted = true;
      }
      processFinished.set(true);
    } catch (InterruptedException e) {
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
