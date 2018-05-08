import edu.kit.iti.formal.automation.Flycheck
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
        try {
            Flycheck.main(arrayOf(file))
        } catch (e: Exception) {
            e.printStackTrace()
        }
    }
}