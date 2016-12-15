package edu.kit.iti.formal.automation.exceptions;

/**
 * @author Alexander Weigl
 * @version 1 (15.12.16)
 */
public class UnknownVariableException extends RuntimeException{
    public UnknownVariableException() {
        super();
    }

    public UnknownVariableException(String message) {
        super(message);
    }

    public UnknownVariableException(String message, Throwable cause) {
        super(message, cause);
    }

    public UnknownVariableException(Throwable cause) {
        super(cause);
    }

    protected UnknownVariableException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}
