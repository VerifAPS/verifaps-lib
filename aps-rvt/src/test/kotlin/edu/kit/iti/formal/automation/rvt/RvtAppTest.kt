package edu.kit.iti.formal.automation.rvt

import org.junit.Assert.*
import org.junit.Test

/**
 * @author Alexander Weigl
 * @version 1 (14.09.17)
 */
class RvtAppTest {
    @Test
    fun testVerifySimple(): Unit {
        val old = "src/test/resources/simple1_new.st"
        val new = "src/test/resources/simple1_old.st"

        val app = RvtApp(old, new)

        app.build()
        app.verify()
    }
}