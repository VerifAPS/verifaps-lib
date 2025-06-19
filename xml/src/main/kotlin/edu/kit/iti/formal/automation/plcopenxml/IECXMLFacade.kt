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
package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.util.CodeWriter
import java.io.*
import java.net.URL
import java.nio.file.Path
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (15.06.17)
 * @version 2 (22.07.18)
 */
object IECXMLFacade {
    fun extractPLCOpenXml(url: URL, sink: Writer) {
        PCLOpenXMLBuilder(url, CodeWriter(sink)).run()
        sink.flush()
    }

    fun extractPLCOpenXml(filename: String, sink: Writer) = extractPLCOpenXml(File(filename), sink)
    fun extractPLCOpenXml(filename: File, sink: Writer) = extractPLCOpenXml(filename.toURI().toURL(), sink)
    fun extractPLCOpenXml(filename: Path, sink: Writer) = extractPLCOpenXml(filename.toUri().toURL(), sink)

    fun extractPLCOpenXml(filename: URL): String {
        val writer = StringWriter()
        extractPLCOpenXml(filename, writer)
        return writer.toString()
    }

    fun extractPLCOpenXml(filename: String) = extractPLCOpenXml(File(filename))
    fun extractPLCOpenXml(filename: File) = extractPLCOpenXml(filename.toURI().toURL())
    fun extractPLCOpenXml(filename: Path) = extractPLCOpenXml(filename.toUri().toURL())

    val SFC_KEYWORDS = setOf("step", "end_step", "transition", "end_transition")
    fun quoteVariable(name: String): String = if (name.lowercase(Locale.getDefault()) in
        SFC_KEYWORDS
    ) {
        "`$name`"
    } else {
        name
    }

    fun quoteStBody(body: String): String = body.replace("\\b\\w+\\b".toRegex()) {
        quoteVariable(it.value)
    }
}