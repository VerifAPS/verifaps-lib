package edu.kit.iti.formal.automation

import com.google.common.truth.Truth
import org.antlr.v4.runtime.CharStreams
import org.junit.Assert
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

object ModuleBuilderRegressionTests {
    @Test
    fun specialStatements() {
        val expected = javaClass.getResourceAsStream("/edu/kit/iti/formal/automation/st/specialstatements.smv")
                ?.bufferedReader()?.readText()?:""
        val (stInput,_) =
                IEC61131Facade.fileResolve(
                        CharStreams.fromStream(
                                javaClass.getResourceAsStream("/edu/kit/iti/formal/automation/st/specialstatements.st")))
        Assertions.assertNotNull(expected)
        Assertions.assertNotNull(stInput)
        println(IEC61131Facade.print(stInput))

        val mod = SymbExFacade.evaluateProgram(stInput, true)

        val actual = mod.repr()
        Assertions.assertEquals(cleanWs(expected), cleanWs(actual))
    }

    private fun cleanWs(s: String) = s.replace("\\s+".toRegex(), "\n")
}
