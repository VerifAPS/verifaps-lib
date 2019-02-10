import edu.kit.iti.formal.smt.CliSmtSolverImpl
import edu.kit.iti.formal.smt.InteractiveSmtSolverImpl
import edu.kit.iti.formal.util.findProgram
import org.junit.Assert
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
        solver.send("""
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
                """)

        val isSat1 = solver.read()
        val model1 = solver.read()

        solver.send("""
        (push)
        (assert (= x y))
        (check-sat)
        (get-model)""")

        val isSat2 = solver.read()
        Assert.assertEquals("sat", isSat1.toString())
        Assert.assertEquals("unsat", isSat2.toString())

        println(isSat1)
        println(model1)
        println(isSat2)

        solver.dispose()
        //not working always:
        // Assert.assertFalse(solver.process!!.isAlive)
    }

    @Test
    fun testZ3Cli() {
        val z3 = findProgram("z3")
        Assumptions.assumeTrue(z3 != null)
        val solver = CliSmtSolverImpl.getZ3()
        solver.send("""
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
                (check-sat)""")

        solver.run(10, TimeUnit.SECONDS)
        val (isSat1, model1, isSat2) = solver.readAll()

        Assert.assertEquals("sat", isSat1.toString())
        Assert.assertEquals("unsat", isSat2.toString())

        println(isSat1)
        println(model1)
        println(isSat2)
    }
}
