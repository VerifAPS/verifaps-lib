import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.modularization.CallSiteFinder
import edu.kit.iti.formal.automation.visitors.Utils
import org.antlr.v4.runtime.CharStreams
 import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (14.07.18)
 */
class ModularizationAppTest {
    fun testListCallSite(p: String) {
        val (p, e) =
                IEC61131Facade.fileResolve(CharStreams.fromStream(
                        javaClass.getResourceAsStream(p)))
        val cfs = CallSiteFinder(Utils.findProgram(p)!!, p)
        cfs.run()
        cfs.callSites.forEach {
            println(it.repr())
        }
    }

/*    @Test
    fun listCallSites0() = testListCallSite("/program.st")

    @Test
    fun listCallSites1() = testListCallSite("/program1.st")

    @Test
    fun listCallSites2() = testListCallSite("/program2.st")
*/
    @Test
    fun listCallSites3() = testListCallSite("/scenario0.st")

    @Test
    fun listCallSites4() = testListCallSite("/scenario1.st")
}