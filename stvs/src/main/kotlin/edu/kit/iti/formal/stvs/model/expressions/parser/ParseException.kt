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
package edu.kit.iti.formal.stvs.model.expressions.parser

/**
 * An Exception for parsing errors.
 *
 * @author Philipp
 */
data class ParseException
/**
 * Any kind of parsing exception for human-readable files.
 *
 * @param line the first line the error occured
 * @param characterInLine the first character of the character in the line.
 * @param parseErrorMessage an error message to provide further information to the user.
 */
    (
    val line: Int,
    val characterInLine: Int,
    val parseErrorMessage: String
) : Exception("(line $line character $characterInLine): $parseErrorMessage")