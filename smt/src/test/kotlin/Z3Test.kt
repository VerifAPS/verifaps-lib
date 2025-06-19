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
import edu.kit.iti.formal.smt.CliSmtSolverImpl
import edu.kit.iti.formal.smt.InteractiveSmtSolverImpl
import edu.kit.iti.formal.util.findProgram
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.Test
import java.util.concurrent.TimeUnit

/**
 *
 * @author Alexander Weigl
 * @version 1 (25.01.19)
 */
class Z3Test {
    @Test
    fun testZ3Interactive() {
        val z3 = findProgram("z3")
        Assumptions.assumeTrue { z3 != null }
        val solver = InteractiveSmtSolverImpl.getZ3()
        solver.start()
        solver.send(
            """
                ; This example illustrates basic arithmetic and
                ; uninterpreted functions
                (declare-fun x () Int)
                (declare-fun y () Int)
                (declare-fun z () Int)
                (assert (>= (* 2 x) (+ y z)))
                (declare-fun f (Int) Int)
                (declare-fun g (Int Int) Int)
                (assert (< (f x) (g x x)))
                (assert (> (f y) (g x x)))
                (check-sat)
                (get-model)
                """,
        )

        val isSat1 = solver.read()
        val model1 = solver.read()

        solver.send(
            """
        (push)
        (assert (= x y))
        (check-sat)
        (get-model)""",
        )

        val isSat2 = solver.read()
        Assertions.assertEquals("sat", isSat1.toString())
        Assertions.assertEquals("unsat", isSat2.toString())

        println(isSat1)
        println(model1)
        println(isSat2)

        solver.dispose()
        // not working always:
        // Assertions.assertFalse(solver.process!!.isAlive)
    }

    @Test
    fun testZ3Cli() {
        val z3 = findProgram("z3")
        Assumptions.assumeTrue(z3 != null)
        val solver = CliSmtSolverImpl.getZ3()
        solver.send(
            """
                ; This example illustrates basic arithmetic and
                ; uninterpreted functions
                (declare-fun x () Int)
                (declare-fun y () Int)
                (declare-fun z () Int)
                (assert (>= (* 2 x) (+ y z)))
                (declare-fun f (Int) Int)
                (declare-fun g (Int Int) Int)
                (assert (< (f x) (g x x)))
                (assert (> (f y) (g x x)))
                (check-sat)
                (get-model)
                (push)
                (assert (= x y))
                (check-sat)""",
        )

        solver.run(10, TimeUnit.SECONDS)
        val (isSat1, _, isSat2) = solver.readAll()

        Assertions.assertEquals("sat", isSat1.toString())
        Assertions.assertEquals("unsat", isSat2.toString())
    }
}
