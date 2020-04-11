package edu.kit.iti.formal.automation.rvt.modularization

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.visitors.findProgram
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
        val cfs = CallSiteFinder(findProgram(p)!!)
        cfs.run()
        cfs.callSites.forEach {
            println(it.repr())
        }
    }

    @Test
    fun listCallSites0() = testListCallSite("/modularization/program.st")

    @Test
    fun listCallSites1() = testListCallSite("/modularization/program1.st")

    @Test
    fun listCallSites2() = testListCallSite("/modularization/program2.st")

    @Test
    fun listCallSites3() = testListCallSite("/modularization/scenario0.st")

    @Test
    fun listCallSites4() = testListCallSite("/modularization/scenario1.st")
}