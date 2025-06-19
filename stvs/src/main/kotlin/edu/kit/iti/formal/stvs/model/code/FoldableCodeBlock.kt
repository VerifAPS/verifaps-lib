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

/**
 * A block of source code. Although code folding is not supported by the view, this class may be
 * used in future versions to implement code folding.
 *
 * @author Philipp
 */
data class FoldableCodeBlock(
    /**
     * Get the index of the last line of the code block.
     * @return The index of the first line of the code block
     */
    val startLine: Int,
    /**
     * Get the index of the first line of the code block.
     * @return The index of the first line of the code block
     */
    val endLine: Int,
)