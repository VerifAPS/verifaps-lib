package edu.kit.iti.formal.automation.exceptions;

/**
 * Created by weigl on 27.11.16.
 */
public class OperatorNotFoundException extends SMVException {
    public OperatorNotFoundException() {
        super();
    }

    public OperatorNotFoundException(String message) {
        super(message);
    }

    public OperatorNotFoundException(String message, Throwable cause) {
        super(message, cause);
    }

    public OperatorNotFoundException(Throwable cause) {
        super(cause);
    }

    protected OperatorNotFoundException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}
