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
package edu.kit.iti.formal.automation.xml

import LoadHelp
import edu.kit.iti.formal.automation.plcopenxml.FBDTranslator
import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import edu.kit.iti.formal.automation.plcopenxml.PCLOpenXMLBuilder
import edu.kit.iti.formal.util.CodeWriter
import org.jdom2.filter.Filters
import org.jdom2.input.SAXBuilder
import org.jdom2.xpath.XPathFactory
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.Test
import java.io.StringWriter
import java.nio.file.Files

/**
 *
 * @author Alexander Weigl
 * @version 1 (27.02.19)
 */
object FBDTest {
    @Test
    fun fbdExampleDotFile() {
        val path = LoadHelp.getResource("FBDExample.xml")
        Assumptions.assumeTrue(path != null)
        val saxBuilder = SAXBuilder()
        saxBuilder.saxHandlerFactory = PCLOpenXMLBuilder.FACTORY
        val doc = saxBuilder.build(path?.toUri()?.toURL())
        val xpathFactory = XPathFactory.instance()
        val pou = xpathFactory.compile("//pou[@name=\"FBD1\"]/body/FBD", Filters.element()).evaluateFirst(doc)
        Assumptions.assumeTrue(pou != null)

        val t = FBDTranslator(pou, CodeWriter())
        val body = t.generateFbdBody()
        val c = CodeWriter()
        body.writeDot(c)
        body.asStructuredText(c)
        println(c.stream.toString())
    }

    @Test
    fun fbdExample() {
        val path = LoadHelp.getResource("FBDExample.xml")
        Assumptions.assumeTrue(path != null)
        val out = IECXMLFacade.extractPLCOpenXml(path!!)
        println(out)
    }

    @Test
    fun pclOpenXmlTest() {
        val path = LoadHelp.getResource("pclopen_fbd_example.xml")
        Assumptions.assumeTrue(path != null)
        val saxBuilder = SAXBuilder()
        val element = saxBuilder.build(Files.newBufferedReader(path)).rootElement
        val sw = StringWriter()
        FBDTranslator(element, CodeWriter(sw)).run()
        println(sw)
    }
}
