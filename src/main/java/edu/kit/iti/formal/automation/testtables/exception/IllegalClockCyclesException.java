package edu.kit.iti.formal.automation.testtables.exception;

/**
 * @author Alexander Weigl
 * @version 1 (24.12.16)
 */
public class IllegalClockCyclesException extends RuntimeException {
    public IllegalClockCyclesException() {
        super();
    }

    public IllegalClockCyclesException(String message) {
        super(message);
    }

    public IllegalClockCyclesException(String message, Throwable cause) {
        super(message, cause);
    }

    public IllegalClockCyclesException(Throwable cause) {
        super(cause);
    }

    protected IllegalClockCyclesException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}
