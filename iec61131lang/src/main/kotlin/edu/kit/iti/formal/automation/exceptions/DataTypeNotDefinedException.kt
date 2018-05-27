package edu.kit.iti.formal.automation.exceptions

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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

/**
 * @author weigl
 * @version $Id: $Id
 * @since 25.11.16
 */
class DataTypeNotDefinedException : RuntimeException {
    /**
     *
     * Constructor for DataTypeNotDefinedException.
     */
    constructor() : super() {}

    /**
     *
     * Constructor for DataTypeNotDefinedException.
     *
     * @param message a [java.lang.String] object.
     */
    constructor(message: String) : super(message) {}

    /**
     *
     * Constructor for DataTypeNotDefinedException.
     *
     * @param message a [java.lang.String] object.
     * @param cause   a [java.lang.Throwable] object.
     */
    constructor(message: String, cause: Throwable) : super(message, cause) {}

    /**
     *
     * Constructor for DataTypeNotDefinedException.
     *
     * @param cause a [java.lang.Throwable] object.
     */
    constructor(cause: Throwable) : super(cause) {}

    /**
     *
     * Constructor for DataTypeNotDefinedException.
     *
     * @param message            a [java.lang.String] object.
     * @param cause              a [java.lang.Throwable] object.
     * @param enableSuppression  a boolean.
     * @param writableStackTrace a boolean.
     */
    protected constructor(message: String, cause: Throwable, enableSuppression: Boolean, writableStackTrace: Boolean) : super(message, cause, enableSuppression, writableStackTrace) {}
}
