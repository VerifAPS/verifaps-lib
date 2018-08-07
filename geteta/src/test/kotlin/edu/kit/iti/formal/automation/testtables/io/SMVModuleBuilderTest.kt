/**
 * geteta
 *
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl></weigl>@kit.edu>
 *
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http:></http:>//www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.io

import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.builder.TableTransformation
import org.junit.Assert
import org.junit.Test

import javax.xml.bind.JAXBException
import java.io.IOException

/**
 * @author Alexander Weigl
 * @version 1 (02.02.18)
 */
class SMVModuleBuilderTest {
    @Test
    @Throws(JAXBException::class, IOException::class)
    fun testDetWait1() {
        test("src/test/resources/detwait/detwait1.xml",
                "src/test/resources/detwait/detwait1.smv")
    }

    @Test
    @Throws(JAXBException::class, IOException::class)
    fun testDetWait2() {
        test("src/test/resources/detwait/detwait2.xml",
                "src/test/resources/detwait/detwait2.smv")
    }

    @Test
    @Throws(JAXBException::class, IOException::class)
    fun testDetWait3() {
        test("src/test/resources/detwait/detwait3.xml",
                "src/test/resources/detwait/detwait1.smv")
    }


    @Test
    @Throws(JAXBException::class, IOException::class)
    fun testOmega1() {
        test("src/test/resources/omega/simplify1.xml",
                "src/test/resources/omega/simplify1.smv")
    }


    @Throws(JAXBException::class, IOException::class)
    fun test(table: String, expectedSMVFile: String) {
        val gtt = GetetaFacade.parseTableXML(table)
        val expected = java.io.File(expectedSMVFile).readText()
        val enumType = GetetaFacade.createSuperEnum(listOf(Scope()))
        val tt = TableTransformation(gtt, enumType, true)
        val module = tt.transform()
        val output = module.toString()
        Assert.assertEquals(expected, output)
    }
}
