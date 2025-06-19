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
package edu.kit.iti.formal.automation.rvt.modularization

/**
 * @author Alexander Weigl
 * @version 1 (01.02.19)
 */
class ProofExecutorTest {
    /*fun testMock() {
        class DummyTask(val ms: Long, message: String) : ProofTask() {
            init {
                desc = message
            }

            override fun init() {}
            override fun prove(): Boolean? {
                Thread.sleep(ms)
                return true
            }
        }

        val a = DummyTask(100, "A")
        val b = DummyTask(100, "B")
        val c = DummyTask(100, "C")
        val d = DummyTask(100, "D")
        val e = DummyTask(100, "E")
        val f = DummyTask(100, "F")
        val g = DummyTask(100, "G")

        g.predecessors.add(f)
        f.predecessors.add(e)
        e.predecessors.add(d)
        d.predecessors.add(c)
        c.predecessors.add(b)
        b.predecessors.add(a)

        val tasks = listOf(a, b, c, d, e, f, g)
        val pe = ProofExecutor(tasks)
        pe.start()//blocks
        tasks.forEach { Assertions.assertEquals(ProofTaskState.FINISHED_VALID, it.state) }
    }*/
}
