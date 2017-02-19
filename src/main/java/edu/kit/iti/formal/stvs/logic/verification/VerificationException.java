package edu.kit.iti.formal.stvs.logic.verification;

/**
 * Created by bal on 11.02.17.
 * @author Benjamin Alt
 */
public class VerificationException extends Exception {

  private Reason reason;

  public VerificationException(Reason reason) {
    this.reason = reason;
  }

  public Reason getReason() {
    return reason;
  }

  public enum Reason {GETETA_NOT_FOUND, NUXMV_NOT_FOUND}
}
