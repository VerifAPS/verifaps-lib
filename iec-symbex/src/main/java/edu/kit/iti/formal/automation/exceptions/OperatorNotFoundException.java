package edu.kit.iti.formal.automation.exceptions;

/*-
 * #%L
 * iec-symbex
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
