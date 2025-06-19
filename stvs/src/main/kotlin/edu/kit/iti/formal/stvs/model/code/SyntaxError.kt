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
package edu.kit.iti.formal.stvs.model.code

import org.antlr.v4.runtime.Token

/**
 * Represents a syntax error in code.
 * @param line the line of the token with the syntax error
 * @param charPos the char position of the token with the syntax error
 * @param message the error message
 * @author Lukas Fritsch
 */
class SyntaxError(@JvmField val line: Int, val charPos: Int, @JvmField val message: String) {
    fun isToken(token: Token): Boolean = (line == token.line) && (charPos == token.charPositionInLine)

    override fun toString(): String = "Error at ($line,$charPos): $message"
}