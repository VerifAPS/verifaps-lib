package edu.kit.iti.formal.automation.exceptions;

/**
 * Created by weigl on 25.11.16.
 */
public class DataTypeNotDefinedException extends RuntimeException {
    public DataTypeNotDefinedException() {
        super();
    }

    public DataTypeNotDefinedException(String message) {
        super(message);
    }

    public DataTypeNotDefinedException(String message, Throwable cause) {
        super(message, cause);
    }

    public DataTypeNotDefinedException(Throwable cause) {
        super(cause);
    }

    protected DataTypeNotDefinedException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}
