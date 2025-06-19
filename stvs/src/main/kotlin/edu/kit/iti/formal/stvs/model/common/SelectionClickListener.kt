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
package edu.kit.iti.formal.stvs.model.common

/**
 * `SelectionClickListener` gets invoked by [Selection] and indicates that the user
 * clicked on a view (such as a region in a timing diagram) that represents a cell in the
 * [edu.kit.iti.formal.stvs.model.table.HybridSpecification].
 */
fun interface SelectionClickListener {
    /**
     * Must handle a click event that can be assigned to a cell in a
     * [edu.kit.iti.formal.stvs.model.table.HybridSpecification]
     *
     * @param columnName Name of the column that the event can be assigned to
     * @param rowNumber Number of the row that the event can be assigned to
     */
    fun clicked(columnName: String?, rowNumber: Int?)
}