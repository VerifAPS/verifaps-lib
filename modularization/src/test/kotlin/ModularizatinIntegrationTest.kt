import edu.kit.iti.formal.automation.modularization.ModApp
 import org.junit.jupiter.api.Test
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (16.07.18)
 */
class ModularizationIntegrationTest {
    //TODO @Test
    fun testProgram(): Unit {
        val old = File("src/test/resources/program1.st").absolutePath
        val new = File("src/test/resources/program2.st").absolutePath
        val args = arrayOf("--old", old, "--new", new, "-o", "build/testProgram",
                "-s", "PGRM.INST_A.0=PGRM.INST_A.0",
                "-s", "PGRM.INST_B.0=PGRM.INST_B.0")
        ModApp.main(args)
    }

    //TODO @Test
    fun testScenario(): Unit {
        val old = File("src/test/resources/scenario1.st").absolutePath
        val new = File("src/test/resources/scenario0.st").absolutePath
        val args = arrayOf("--old", old, "--new", new, "-o", "build/testScenario",
                "-s", "Main.Mag.0=Main.Mag.0",
                "-s", "Main.Crane.0=Main.Crane.0"
        )
        ModApp.main(args)
    }
}