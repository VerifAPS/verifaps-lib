package edu.kit.iti.formal.automation.testtables.apps

import org.junit.jupiter.api.Test
import java.io.StringWriter

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/25/20)
 */
internal class CsvTranslatorTest {
    @Test fun simpleTest() {
        val csvInput = """
            in I : INT,out O : BOOL,DURATION
            =2,=TRUE, 1
            =I[-1],-,>=0
            =2+2, =I>5,"[3,5]"
            "=2+2,I%2=0",-,omega
        """.trimIndent()


        val out = StringWriter()
        val t= CsvTranslator(out, "\"", ",")
        t.run("test", csvInput)
        println(out.toString())
    }
}