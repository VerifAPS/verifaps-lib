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
package edu.kit.iti.formal.stvs.model.config

import javafx.beans.property.SimpleDoubleProperty

/**
 * Configuration for table column. Contains GUI-related information about a column.
 *
 * @author Philipp
 */
class ColumnConfig {
    private val widthProperty = SimpleDoubleProperty(100.0)
    var width: Double
        get() = widthProperty.get()
        set(value) {
            require(value >= 0)
            widthProperty.set(value)
        }

    /**
     * Create a new ColumnConfig.
     *
     * @param colwidth The initial column width
     */
    constructor(colwidth: Double = 100.0) {
        require(!(colwidth <= 0)) { "Column width must be positive" }
        width = colwidth
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ColumnConfig) return false

        if (width != other.width) return false

        return true
    }

    override fun hashCode(): Int = width.hashCode()
}