package edu.kit.iti.formal.automation

import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import java.io.File
import java.io.FilenameFilter

/**
 *
 * @author Alexander Weigl
 * @version 1 (25.04.19)
 */
class XPpuTest{
    @TestFactory
    fun createPPUScenarios(): List<DynamicTest> =
            File("../share/xPPU/")
                    .listFiles { dir, name -> name.endsWith("xml") }
                    .map {
                        DynamicTest.dynamicTest(it.name) {
                            runPPU(it)
                        }
                    }

    private fun runPPU(it: File) {
        println(it)
        val elements = IEC61131Facade.file(it,true)
    }
}