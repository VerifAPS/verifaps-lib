package edu.kit.iti.formal.automation.rvt.modularization

import org.junit.jupiter.api.Test
import java.io.File

const val base = "src/test/resources/modularization"

/**
 *
 * @author Alexander Weigl
 * @version 1 (16.07.18)
 */
class ModularizationIntegrationTest {
    @Test
    fun testProgram() {
        val old = File("$base/program1.st").absolutePath
        val new = File("$base/program2.st").absolutePath
        val args = arrayOf("--old", old, "--new", new, "-o", "build/testProgram",
                "-s", "PGRM.INST_A.0=PGRM.INST_A.0",
                "-s", "PGRM.INST_B.0=PGRM.INST_B.0")
        ModApp.main(args)
    }

    @Test
    fun testScenario() {
        val old = File("$base/scenario1.st").absolutePath
        val new = File("$base/scenario0.st").absolutePath
        val args = arrayOf("--old", old, "--new", new, "-o", "build/testScenario",
                "-s", "Main.Mag.0=Main.Mag.0",
                "-s", "Main.Crane.0=Main.Crane.0"
        )
        ModApp.main(args)
    }

    @Test
    fun testSimple() {
        val input = File("$base/simpleA.st").absolutePath
        val args = arrayOf("--old", "A@$input", "--new", "B@$input",
                "-o", "build/testScenario/simple",
                "-s", "A.f1.0=B.f1.0",
                "-s", "A.f2.0=B.f2.0"
        )
        ModApp.main(args)
    }

    @Test
    fun testComplexArithmetic() {
        val input = File("$base/complex_arithmetic.st").absolutePath
        val args = arrayOf("--old", "WARN_ABOVE@$input", "--new", "WARN_BELOW@$input",
                "-o", "build/testScenario/simple",
                "-s", "WARN_ABOVE.sm.0=WARN_BELOW.sm.0##",
                "-ri", "threshold=threshold&sensor=sensor",
                "-ro", "critical=!critical"
        )
        ModApp.main(args)
    }


    @Test
    fun testSimpleCtx() {
        val input = File("$base/simpleA.st").absolutePath
        val args = arrayOf("--old", "A@$input", "--new", "B@$input",
                "-o", "build/testScenario/simple",
                "-fc", "A.f1.0=B.f1.0##",
                "-fc", "A.f2.0=B.f2.0##",
                "--info"
        )
        ModApp.main(args)
    }
}