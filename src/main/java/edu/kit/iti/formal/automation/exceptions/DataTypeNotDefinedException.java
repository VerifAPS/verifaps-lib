package edu.kit.iti.formal.automation.exceptions;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

/**
 * Created by weigl on 25.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class DataTypeNotDefinedException extends RuntimeException {
    /**
     * <p>Constructor for DataTypeNotDefinedException.</p>
     */
    public DataTypeNotDefinedException() {
        super();
    }

    /**
     * <p>Constructor for DataTypeNotDefinedException.</p>
     *
     * @param message a {@link java.lang.String} object.
     */
    public DataTypeNotDefinedException(String message) {
        super(message);
    }

    /**
     * <p>Constructor for DataTypeNotDefinedException.</p>
     *
     * @param message a {@link java.lang.String} object.
     * @param cause a {@link java.lang.Throwable} object.
     */
    public DataTypeNotDefinedException(String message, Throwable cause) {
        super(message, cause);
    }

    /**
     * <p>Constructor for DataTypeNotDefinedException.</p>
     *
     * @param cause a {@link java.lang.Throwable} object.
     */
    public DataTypeNotDefinedException(Throwable cause) {
        super(cause);
    }

    /**
     * <p>Constructor for DataTypeNotDefinedException.</p>
     *
     * @param message a {@link java.lang.String} object.
     * @param cause a {@link java.lang.Throwable} object.
     * @param enableSuppression a boolean.
     * @param writableStackTrace a boolean.
     */
    protected DataTypeNotDefinedException(String message, Throwable cause, boolean enableSuppression, boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }
}
