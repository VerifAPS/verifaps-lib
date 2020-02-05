package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.IEC61131Facade
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (12.11.19)
 */
internal class UnfoldStateTest {
    @Test
    fun testArrayRecordInit() {
        val res = javaClass.getResourceAsStream("/edu/kit/iti/formal/automation/st/ai_complex1_test.st")!!
        val pous = IEC61131Facade.fileResolve(CharStreams.fromStream(res))
        Assertions.assertEquals(0, pous.second.size)
        Assertions.assertEquals(6, pous.first.size)
        val us = UnfoldState()
        us.addPous(pous.first)
        val state = us.state

        for ((k, v) in state) {
            println("$k = $v")
        }

        for ((k, v) in us.decls) {
            println("$k = $v")
        }

        us.classInstances()

    }

}

