package edu.kit.iti.formal.automation.rvt

import org.apache.commons.io.FileUtils
import org.junit.Test

import org.junit.Assert.*

/**
 * @author Alexander Weigl
 * @version 1 (14.09.17)
 */
class McKtTest {
    @Test
    fun testParseOutput() {
        val resource = javaClass.getResource("/cex.xml")
        val xml = resource.readText()
        val out =parseOutput(xml)
        assertFalse(out.hasErrors)
        assertEquals(0, out.errors.size)
        assertNotNull(out.counterExample)

        assertEquals(false, out.isVerified)
        println(out.counterExample)
    }

}
