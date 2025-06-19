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

import java.io.InputStream

/**
 * An Interface for all classes concerned with importing model objects from some import format.
 * @param <T> "<u>T</u>o": Generic type parameter for the target type.
 * @author Benjamin Alt
</T> */
interface Importer<T> {
    /**
     * Must implement logic to implement `source`.
     *
     * @param source stream from which the data to import should be read
     * @return the imported object
     * @throws ImportException Exception while importing
     */
    @Throws(ImportException::class)
    fun doImport(source: InputStream): T
}