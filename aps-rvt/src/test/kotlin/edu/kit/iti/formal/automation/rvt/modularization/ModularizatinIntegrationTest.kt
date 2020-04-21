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
}