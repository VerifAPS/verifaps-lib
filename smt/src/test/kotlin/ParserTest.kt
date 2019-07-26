import edu.kit.iti.formal.smt.readFirstSexpr
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory
import java.io.StringReader

/**
 * @author Alexander Weigl
 * @version 1 (11.12.18)
 */
class ParserTest {
    @TestFactory
    fun testReadFirstSexpr(): Collection<DynamicTest> =
            listOf(
                    testReadFirstSexpr("abc", "abc"),
                    testReadFirstSexpr("abc", "abc def"),
                    testReadFirstSexpr("|abc|", "     |abc|"),
                    testReadFirstSexpr("|ab c|", "     |ab c|"),
                    testReadFirstSexpr("(abc)", "(abc) def"),
                    testReadFirstSexpr("(123 (456))", "(123 (456)) 2423424"),
                    testReadFirstSexpr("(123 (456) 789)", "(123 (456) 789) 2423424"),
                    testReadFirstSexpr("abc", "abc (123 (456) 789) 2423424"))

    fun testReadFirstSexpr(exp: String, input: String): DynamicTest =
            DynamicTest.dynamicTest(exp) { Assertions.assertEquals(exp, getSexpr(input)) }

    fun getSexpr(s: String): String =
            readFirstSexpr(StringReader(s))
}