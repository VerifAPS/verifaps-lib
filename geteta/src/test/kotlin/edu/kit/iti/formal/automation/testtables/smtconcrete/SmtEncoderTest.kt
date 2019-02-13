package edu.kit.iti.formal.automation.testtables.smtconcrete

import edu.kit.iti.formal.automation.testtables.GetetaFacade
 import org.junit.jupiter.api.Test
import java.io.File

/**
 * @author Alexander Weigl
 * @version 1 (11.12.18)
 */
class SmtEncoderTest {
    @Test
    fun test() {
        val gtt = GetetaFacade.readTable(File("examples/MinMax/MinMax.tt.txt"))
        gtt.programRuns += ""
        gtt.generateSmvExpression()

        val superEnum = GetetaFacade.createSuperEnum(listOf())
        val smvModel = GetetaFacade.constructSMV(gtt, superEnum)
        val encoder = SmtEncoder(gtt,
                smvModel, 10)
        encoder.run()
        encoder.model.file.forEach {
            println(it)
        }
    }
}