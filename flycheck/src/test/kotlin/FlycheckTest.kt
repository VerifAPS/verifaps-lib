import edu.kit.iti.formal.automation.Check
import java.io.File
import kotlin.test.Test

/**
 *
 * @author Alexander Weigl
 * @version 1 (18.03.18)
 */
class FlycheckTest {
    @Test
    fun test() {
        val file = File("src/test/resources/test.st").absolutePath
        Check.main(arrayOf(file))
    }

    @Test
    fun testOO() {
        val file = File("src/test/resources/testoo.st").absolutePath
        Check.main(arrayOf(file))
    }
}