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

import java.io.ByteArrayOutputStream
import java.io.OutputStream

/**
 * Interface for all classes concerned with exporting model objects to some output format.
 * @param <F> "<u>F</u>rom": Generic type parameter for the source type.
 * @author Benjamin Alt
</F> */
interface Exporter<F> {
    /**
     * Implementations of this method must encode the `source` object. The format for encoding
     * is specified in the implementing classes or their subclasses. The encoded object is then
     * written to the returned [ByteArrayOutputStream].
     *
     * @param source Object that should be exported
     * @return The encoded object is written to this stream.
     * @throws ExportException Exception while exporting
     */
    @Throws(ExportException::class)
    fun export(source: F, target: OutputStream)
}