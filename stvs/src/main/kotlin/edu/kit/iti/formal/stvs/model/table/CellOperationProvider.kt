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
package edu.kit.iti.formal.stvs.model.table

/**
 * Interface for classes that Provide commonly needed functionality for editing, like having a
 * string property and being commentable.
 * @author Benjamin Alt
 */
interface CellOperationProvider :
    Commentable,
    StringEditable {
    /**
     * Prints a minimal string including the string representation and optionally adds the comment, if
     * not null.
     * (should only used for debugging purposes, i.e. in toString methods)
     * @return a minimal string
     */
    fun debuggingString() = asString + (comment?.let { " (comment: \"$it\")" } ?: "")
}