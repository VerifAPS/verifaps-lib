import edu.kit.iti.formal.smt.SmtFacade
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory

/**
 * @author Alexander Weigl
 * @version 1 (13.10.18)
 */
class SmtFacadeTest {
    @TestFactory
    fun intFromHex1Byte(): Collection<DynamicTest> {
        val testcases = (0..255).map {
            it.toBigDecimal() to String.format("#x%02X", it)
        }
        return testcases.map { (a, b) ->
            DynamicTest.dynamicTest(b) {
                val r = SmtFacade.hexFromInt(a.toBigInteger(), 8)
                Assertions.assertEquals(b, r)
            }
        }
    }

    @TestFactory
    fun intFromHex1ByteNeg(): Collection<DynamicTest> {
        val testcases = ((-1).downTo(-128)).map {
            it.toBigDecimal() to String.format("#x%02X", 256 + it)
        }
        return testcases.map { (a, b) ->
            DynamicTest.dynamicTest(b) {
                val r = SmtFacade.hexFromInt(a.toBigInteger(), 8)
                Assertions.assertEquals(b, r)
            }
        }
    }

    @TestFactory
    fun testIntToHex4Bytes(): List<DynamicTest> {
        val testcases = arrayOf(
                32767 to "#x7FFF",
                -32768 to "#x8000",
                0 to "#x0000",
                -1 to "#xFFFF",
                32768 to "#x8000",
                65535 to "#xFFFF")
        return testcases.map { (a, b) ->
            DynamicTest.dynamicTest(b) {
                val r = SmtFacade.hexFromInt(a.toBigInteger(), 2 * 8)
                Assertions.assertEquals(b, r)
            }
        }
    }


    /*
    @Test
    fun testReverse() {
        for (i in -32768..32767) {
            assertEquals(i, BitvectorUtils.intFromHex(BitvectorUtils.hexFromInt(i, 4), true))
        }
        for (i in 0..65535) {
            assertEquals(i, BitvectorUtils.intFromHex(BitvectorUtils.hexFromInt(i, 4), false))
        }
    }*/

}