/**
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl></weigl>@kit.edu>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http:></http:>//www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.io

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.algorithms.StateReachability
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import org.junit.After
import org.junit.Assert
import org.junit.Test
import javax.xml.bind.JAXBException

/**
 * @author Alexander Weigl
 * @version 1 (02.02.18)
 */
class TableRowReachabilityTest {
    @After
    fun reporting() {
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachabilityDetWait1() {
        val gtt = GetetaFacade.parseTableXML("src/test/resources/detwait/detwait1.xml")
        val out = getReachabilityString(gtt)
        Assert.assertEquals(
                "s01#(s02)\ns02#(END)", out)
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachabilityDetWait2() {
        val gtt = GetetaFacade.parseTableXML("src/test/resources/detwait/detwait2.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("s01#(s02,s03)\n" +
                "s02#(s03)\n" +
                "s03#(END)", out)
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachabilityDetWait3() {
        val gtt = GetetaFacade.parseTableXML("src/test/resources/detwait/detwait3.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("s01#(s02,s03,s04,s05,s06)\n" +
                "s02#(s03,s04,s05,s06)\n" +
                "s03#(s04,s05,s06)\n" +
                "s04#(s05,s06)\n" +
                "s05#(s06)\n" +
                "s06#(END)", out)
    }


    @Test
    @Throws(JAXBException::class)
    fun testReachabilityOmega1() {
        val gtt = GetetaFacade.parseTableXML("src/test/resources/omega/reachability1.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("s01#(s02)\n" +
                "s02#(s03,s04)\n" +
                "s03#(s04)\n" +
                "s04#()", out)
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachability1() {
        val gtt = GetetaFacade.parseTableXML("src/test/resources/reachability/reachability1.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("s01#(s02)\n" +
                "s02#(s03,s04)\n" +
                "s03#(s04)\n" +
                "s04#(END)", out)
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachability4() {
        val gtt = GetetaFacade.parseTableXML("src/test/resources/reachability/reachability4.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("s01#(s03)\n" +
                "s03#(s05)\n" +
                "s05#(s03,s07)\n" +
                "s07#(s05,s09)\n" +
                "s09#(s07,s09,s10)\n" +
                "s10#(s11,s12)\n" +
                "s11#(s12)\n" +
                "s12#(END)", out)
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachability2() {
        val gtt = GetetaFacade.parseTableXML("src/test/resources/reachability/reachability2.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("s01#(s02,s03,s04)\n" +
                "s02#(s03,s04)\n" +
                "s03#(s04)\n" +
                "s04#(END)", out)
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachability3() {
        val gtt = GetetaFacade.parseTableXML("src/test/resources/reachability/reachability3.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("s01#(s07)\n" +
                "s07#(s07,s08)\n" +
                "s08#(s09,s10)\n" +
                "s09#(s10)\n" +
                "s10#(END)", out)
    }


    @Test
    @Throws(JAXBException::class)
    fun testReachability5() {
        val gtt = GetetaFacade.parseTableXML("src/test/resources/reachability/reachability5.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("s01#(s03)\n" +
                "s03#(s03,s04)\n" +
                "s04#(END)", out)
    }


    fun getReachabilityString(gtt: GeneralizedTestTable): String {
        val sentinelState = TableRow("SENTINEL")
        val reachable: StateReachability = StateReachability(gtt.region)

        return gtt.region.flat()
                .joinToString("\n") { s ->
                    s.id + s.outgoing
                            .map { it.id }
                            .sorted()
                            .joinToString(",", "#(", ")")
                }
    }
}