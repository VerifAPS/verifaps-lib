/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.stvs.logic.io

/**
 * Indicates that an error occurred during exporting.
 *
 * @author Benjamin Alt
 */
class ExportException : Exception {

    /**
     * Create a new ExportException with a given error message.
     * @param message The error message
     */
    constructor(message: String?) : super(message, null)

    /**
     * Create a new ExportException from an exception (e.g. an exception that was thrown and caught
     * during export).
     * @param exception The original exception
     */
    constructor(exception: Exception?) : super(exception)
}