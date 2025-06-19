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
package edu.kit.iti.formal.automation.testtables.builder

import edu.kit.iti.formal.automation.testtables.model.*
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (23.09.19)
 */
internal class RowGroupExpanderTest {
    val r1 = TableRow("a")
    val r2 = TableRow("b")
    val r3 = TableRow("c")
    val r4 = TableRow("d")

    init {
        r1.duration = Duration.OpenInterval(1)
        r2.duration = Duration.OpenInterval(2)
        r3.duration = Duration.OpenInterval(3)
        r4.duration = Duration.OpenInterval(4)
    }

    private fun forHuman(t: TableNode): String = when (t) {
        is TableRow -> "${t.id}::${t.duration.repr()}"
        is Region -> t.children.joinToString("|", "${t.id}::${t.duration.repr()}(", ")") { forHuman(it) }
    }

    @Test
    fun testExpandRegionOmega() {
        val r = Region("r")
        r.duration = Duration.Omega
        r.children = arrayListOf(r1, r2)
        val t = RowGroupExpander.expand(r)
        // no expansion
        Assertions.assertEquals("r::omega(a::>=1|b::>=2)", forHuman(t))
    }

    @Test
    fun testExpandRegionMin0() {
        val r = Region("r")
        r.duration = Duration.OpenInterval(0)
        r.children = arrayListOf(r1, r2)
        val t = RowGroupExpander.expand(r)
        // no expansion
        Assertions.assertEquals("r::>=0(a::>=1|b::>=2)", forHuman(t))
    }

    @Test
    fun testExpandRegionMin1() {
        val r = Region("r")
        r.duration = Duration.OpenInterval(1)
        r.children = arrayListOf(r1, r2)
        val t = RowGroupExpander.expand(r)
        Assertions.assertEquals("r::[1, 1](r_1::[1, 1](r_1_a::>=1|r_1_b::>=2)|r_2::>=0(r_2_a::>=1|r_2_b::>=2))", forHuman(t))
    }

    @Test
    fun testExpandRegionMin2() {
        val r = Region("r")
        r.duration = Duration.OpenInterval(2)
        r.children = arrayListOf(r1)
        val t = RowGroupExpander.expand(r)
        Assertions.assertEquals("r::[1, 1](r_1::[1, 1](r_1_a::>=1)|r_2::[1, 1](r_2_a::>=1)|r_3::>=0(r_3_a::>=1))", forHuman(t))
    }

    @Test
    fun testExpandRegionMin10() {
        val r = Region("r")
        r.duration = Duration.OpenInterval(10)
        r.children = arrayListOf(r1, r2)
        val t = RowGroupExpander.expand(r)
        Assertions.assertEquals(
            "r::[1, 1](" +
                "r_1::[1, 1](r_1_a::>=1|r_1_b::>=2)" +
                "|r_2::[1, 1](r_2_a::>=1|r_2_b::>=2)" +
                "|r_3::[1, 1](r_3_a::>=1|r_3_b::>=2)" +
                "|r_4::[1, 1](r_4_a::>=1|r_4_b::>=2)" +
                "|r_5::[1, 1](r_5_a::>=1|r_5_b::>=2)" +
                "|r_6::[1, 1](r_6_a::>=1|r_6_b::>=2)" +
                "|r_7::[1, 1](r_7_a::>=1|r_7_b::>=2)" +
                "|r_8::[1, 1](r_8_a::>=1|r_8_b::>=2)" +
                "|r_9::[1, 1](r_9_a::>=1|r_9_b::>=2)" +
                "|r_10::[1, 1](r_10_a::>=1|r_10_b::>=2)" +
                "|r_11::>=0(r_11_a::>=1|r_11_b::>=2))",
            forHuman(t),
        )
    }

    @Test
    fun testExpandRegionMin1Max3() {
        val r = Region("r")
        r.duration = Duration.ClosedInterval(1, 3)
        r.children = arrayListOf(r1)
        val t = RowGroupExpander.expand(r)
        Assertions.assertEquals("r::[1, 1](r_1::[1, 1](r_1_a::>=1)|r_2::[0, 1](r_2_a::>=1)|r_3::[0, 1](r_3_a::>=1))", forHuman(t))
    }

    @Test
    fun testExpandRegionCombined() {
        val r = Region("r")
        val s = Region("s")
        val t = Region("t")
        val u = Region("u")

        r.duration = Duration.Omega
        t.duration = Duration.OpenInterval(2)
        s.duration = Duration.ClosedInterval(1, 2)
        u.duration = Duration.OpenInterval(0)

        r.children = arrayListOf(s)
        s.children = arrayListOf(t, u)
        t.children = arrayListOf(r4)
        u.children.add(r3)
        val a = RowGroupExpander.rewrite(r)
        Assertions.assertEquals(
            "r::omega(s::[1, 1](" +
                "s_1::[1, 1](s_1_t::[1, 1](s_1_t_1::[1, 1](s_1_t_1_d::>=4)|s_1_t_2::[1, 1](s_1_t_2_d::>=4)|s_1_t_3::>=0(s_1_t_3_d::>=4))|s_1_u::>=0(c::>=3))" +
                "|s_2::[0, 1](s_2_t::[1, 1](s_2_t_1::[1, 1](s_2_t_1_d::>=4)|s_2_t_2::[1, 1](s_2_t_2_d::>=4)|s_2_t_3::>=0(s_2_t_3_d::>=4))|s_2_u::>=0(c::>=3))))",
            forHuman(a),
        )
    }
}
