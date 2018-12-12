import edu.kit.iti.formal.smt.SExprFacade
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory

/**
 * @author Alexander Weigl
 * @version 1 (12.12.18)
 */
class SExprFacadeTest {
    private val tests: Collection<String> = listOf(
            "abc",
            "1234",
            "def",
            "(+ 2 2 2 2 2 22 2 2 22 22)",
            "sat",
            "unsat",
            "|abc def|",
            "|def\n\nabc|",
            "(((((((((:bv) (_ BitVec 16)))))))))"
    )

    @TestFactory
    fun factory(): Collection<DynamicTest> =
            tests.map {
                DynamicTest.dynamicTest(it, {
                    test(it)
                })
            }

    private fun test(it: String) {
        val res = SExprFacade.parseExpr(it).toString()
        Assertions.assertEquals(it, res)
    }


}