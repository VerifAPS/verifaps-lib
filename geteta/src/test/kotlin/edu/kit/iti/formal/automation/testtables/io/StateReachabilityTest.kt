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
import edu.kit.iti.formal.automation.testtables.model.State
import org.junit.After
import org.junit.Assert
import org.junit.Test
import javax.xml.bind.JAXBException

/**
 * @author Alexander Weigl
 * @version 1 (02.02.18)
 */
class StateReachabilityTest {
    @After
    fun reporting() {
        /*Report.XML_MODE = false;
        Report.close();*/
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachabilityDetWait1() {
        val gtt = GetetaFacade.readTable("src/test/resources/detwait/detwait1.xml")
        val out = getReachabilityString(gtt)
        Assert.assertEquals("1#(2)\n" + "2#(-1)", out)
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachabilityDetWait2() {
        val gtt = GetetaFacade.readTable("src/test/resources/detwait/detwait2.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("1#(2)\n" +
                "2#(3,4)\n" +
                "3#(4)\n" +
                "4#()", out)
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachabilityDetWait3() {
        val gtt = GetetaFacade.readTable("src/test/resources/detwait/detwait3.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("1#(2)\n" +
                "2#(3,4)\n" +
                "3#(4)\n" +
                "4#()", out)
    }


    @Test
    @Throws(JAXBException::class)
    fun testReachabilityOmega1() {
        val gtt = GetetaFacade.readTable("src/test/resources/omega/reachability1.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("1#(2)\n" +
                "2#(3,4)\n" +
                "3#(4)\n" +
                "4#()", out)
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachability1() {
        val gtt = GetetaFacade.readTable("src/test/resources/reachability/reachability1.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("1#(2)\n" +
                "2#(3,4)\n" +
                "3#(4)\n" +
                "4#(-1)", out)
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachability4() {
        val gtt = GetetaFacade.readTable("src/test/resources/reachability/reachability4.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("1#(3)\n" +
                "3#(5)\n" +
                "5#(3,7)\n" +
                "7#(5,9)\n" +
                "9#(7,9,10)\n" +
                "10#(11,12)\n" +
                "11#(12)\n" +
                "12#(-1)", out)
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachability2() {
        val gtt = GetetaFacade.readTable("src/test/resources/reachability/reachability2.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("1#(2,3,4)\n" +
                "2#(3,4)\n" +
                "3#(4)\n" +
                "4#(-1)", out)
    }

    @Test
    @Throws(JAXBException::class)
    fun testReachability3() {
        val gtt = GetetaFacade.readTable("src/test/resources/reachability/reachability3.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("1#(7)\n" +
                "7#(7,8)\n" +
                "8#(9,10)\n" +
                "9#(10)\n" +
                "10#(-1)", out)
    }


    @Test
    @Throws(JAXBException::class)
    fun testReachability5() {
        val gtt = GetetaFacade.readTable("src/test/resources/reachability/reachability5.xml")
        val out = getReachabilityString(gtt)
        println(out)
        Assert.assertEquals("1#(3)\n" +
                "3#(3,4)\n" +
                "4#(-1)", out)
    }


    fun getReachabilityString(gtt: GeneralizedTestTable): String {
        val sentinelState = State("SENTINEL")
        val reachable: StateReachability = StateReachability(sentinelState, gtt.region)

        return gtt.region!!.flat()
                .joinToString("\n") { s ->
                    s.id + s.outgoing
                            .map { it.id }
                            .joinToString(",", "#(", ")")
                }
    }
}