package edu.kit.iti.formal.automation.rvt

import org.junit.Test
import kotlin.test.assertTrue

/**
 * @author Alexander Weigl
 * @version 1 (14.09.17)
 */
class RvtAppTest {
    @Test
    fun testVerifySimple(): Unit {
        val old = "simple1_new"
        val new = "simple1_old"
        assertEqualBehaviour(old, new)
    }

    @Test
    fun testVerifyCasesIf(): Unit {
        val old = "caseif_old"
        val new = "caseif_new"
        assertEqualBehaviour(old, new)
    }

    private fun assertEqualBehaviour(old: String, new: String) {
        val app = RvtApp("src/test/resources/$old.st",
                        "src/test/resources/$new.st")
        app.build()
        assertTrue(app.verify());
    }
}