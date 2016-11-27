package edu.kit.iti.formal.automation.exceptions;

import org.omg.CORBA.SystemException;

/**
 * Created by weigl on 27.11.16.
 */
public class SMVException extends RuntimeException {
    public SMVException() {
        super();
    }

    public SMVException(String message) {
        super(message);
    }

    public SMVException(String message, Throwable cause) {
        super(message, cause);
    }

    public SMVException(Throwable cause) {
        super(cause);
    }

    protected SMVException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}
