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
 * Indicates that expressions which are not allowed in cell expressions (such as function
 * expressions) are encountered inside cell expressions. Generally thrown on all expressions that
 * the grammar supports, but our program does not (yet).
 *
 * @author Philipp
 */
class UnsupportedExpressionException
/**
 * Create a new UnsupportedExpressionException with a given description.
 * @param unsupportedExpressionDescription The description of the problematic grammar feature
 */
(
    val unsupportedExpressionDescription: String
) : Exception("Unsupported Grammar feature: $unsupportedExpressionDescription")