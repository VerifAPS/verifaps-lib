import edu.kit.iti.formal.automation.modularization.ProofExecutor
import edu.kit.iti.formal.automation.modularization.ProofTaskState
import edu.kit.iti.formal.automation.modularization.ProofTask
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (01.02.19)
 */
class ProofExecutorTest {
    @Test
    fun testMock() {
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
    }
}