import edu.kit.iti.formal.automation.Flycheck
import kotlin.test.Test

/**
 *
 * @author Alexander Weigl
 * @version 1 (18.03.18)
 */


class FlycheckTest {
    @Test
    fun test() {
        Flycheck.main(arrayOf("src/test/resources/test.st"))
    }
}