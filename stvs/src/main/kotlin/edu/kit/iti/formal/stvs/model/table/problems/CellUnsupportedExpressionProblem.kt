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
package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.Selection
import edu.kit.iti.formal.stvs.model.expressions.parser.UnsupportedExpressionException

/**
 * The cell problem analog to the [UnsupportedExpressionException]. Created when expressions
 * with function calls or if guards or similar are encountered which have not yet been implemented.
 *
 * @author Benjamin Alt
 */
data class CellUnsupportedExpressionProblem(
    val exception: UnsupportedExpressionException,
    override val column: String,
    override val row: Int,
) : CellProblem {

    override val errorMessage: String = exception.message ?: ""
    override val location = Selection(column, row)
}