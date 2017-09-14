package edu.kit.iti.formal.automation.rvt

import org.junit.Test
import javax.xml.bind.JAXBContext

/**
 *
 * @author Alexander Weigl
 * @version 1 (12.09.17)
 */

class CexTests {
    @Test
    fun testCexXml() {
        val ctx = JAXBContext.newInstance(CounterExample::class.java)
        val um = ctx.createUnmarshaller()
        val cex = um.unmarshal(CounterExample::class.java.getResource("/cex.xml"))
        println(cex)
    }
}