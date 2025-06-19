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
package edu.kit.iti.formal.automation.testtables

import edu.kit.iti.formal.automation.testtables.algorithms.StateReachability
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (02.02.18)
 */
class TableRowReachabilityTest : TableTester() {

    @Test
    fun testReachabilityDetWait1() {
        val gtt = getTable("detwait1")
        val out = getReachabilityString(gtt)
        Assertions.assertEquals("START#(r02)\nr02#(r03)\nr03#(END)", out)
    }

    @Test
    fun testReachabilityDetWait2() {
        val gtt = getTable("detwait2")
        val out = getReachabilityString(gtt)
        println(out)
        Assertions.assertEquals(
            "START#(r02)\nr02#(r03,r04)\n" +
                "r03#(r04)\n" +
                "r04#(END)",
            out,
        )
    }

    @Test
    fun testReachabilityDetWait3() {
        val gtt = getTable("detwait3")
        val out = getReachabilityString(gtt)
        println(out)
        Assertions.assertEquals(
            "START#(r02,r03,r04,r05,r06,r07)\n" +
                "r02#(r03,r04,r05,r06,r07)\n" +
                "r03#(r04,r05,r06,r07)\n" +
                "r04#(r05,r06,r07)\n" +
                "r05#(r06,r07)\n" +
                "r06#(r07)\n" +
                "r07#(END)",
            out,
        )
    }

    @Test
    fun testReachabilityOmega1() {
        val gtt = getTable("reachability1")
        val out = getReachabilityString(gtt)
        println(out)
        Assertions.assertEquals(
            "START#(r02)\n" +
                "r02#(r03)\n" +
                "r03#(r04,r05)\n" +
                "r04#(r05)\n" +
                "r05#(END)",
            out,
        )
    }

    @Test
    fun testReachability1() {
        val gtt = getTable("reachability1")
        val out = getReachabilityString(gtt)
        println(out)
        Assertions.assertEquals(
            "START#(r02)\n" +
                "r02#(r03)\n" +
                "r03#(r04,r05)\n" +
                "r04#(r05)\n" +
                "r05#(END)",
            out,
        )
    }

    // @Test
    fun testReachability4() {
        val gtt = getTable("reachability4")
        val out = getReachabilityString(gtt)
        println(out)
        Assertions.assertEquals(
            "r01#(r03)\n" +
                "r03#(r05)\n" +
                "r05#(r03,r07)\n" +
                "r07#(r05,r09)\n" +
                "r09#(r07,r09,s10)\n" +
                "s10#(s11,s12)\n" +
                "s11#(s12)\n" +
                "s12#(END)",
            out,
        )
    }

    @Test
    fun testReachability2() {
        val gtt = getTable("reachability2")
        val out = getReachabilityString(gtt)
        println(out)
        Assertions.assertEquals(
            "START#(r02,r03,r04,r05)\n" +
                "r02#(r03,r04,r05)\n" +
                "r03#(r04,r05)\n" +
                "r04#(r05)\n" +
                "r05#(END)",
            out,
        )
    }

    @Test
    fun testReachability3() {
        val gtt = getTable("reachability3")
        val out = getReachabilityString(gtt)
        println(out)
        Assertions.assertEquals(
            "START#(a)\n" +
                "a#(b)\n" +
                "b#(b,c)\n" +
                "c#(d,e)\n" +
                "d#(e)\n" +
                "e#(END)",
            out,
        )
    }

    @Test
    fun testReachability6() {
        val gtt = getTable("reachability6")
        val out = getReachabilityString(gtt)
        Assertions.assertEquals(
            "START#(a,b,c)\n" +
                "a#(b,c)\n" +
                "b#(c)\n" +
                "c#(END)",
            out,
        )
    }

    fun getReachabilityString(gtt: GeneralizedTestTable): String {
        val reachable: StateReachability = StateReachability(gtt.region)
        val states = listOf(reachable.startSentinel) + gtt.region.flat()

        return states
            .joinToString("\n") { s ->
                s.id + s.outgoing
                    .map { it.id }
                    .sorted()
                    .joinToString(",", "#(", ")")
            }
    }
}