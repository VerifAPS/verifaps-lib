import edu.kit.iti.formal.automation.modularization.ModularizationApp
import org.junit.Test
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (16.07.18)
 */
class ModularizatinIntegrationTest{
    @Test
    fun testProgram(): Unit {
        val old = File("src/test/resources/program1.st").absolutePath
        val new = File("src/test/resources/program2.st").absolutePath
        val args = arrayOf("--old", old, "--new", new)
        ModularizationApp.main(args)
    }

    @Test
    fun testScenario(): Unit {

    }
}