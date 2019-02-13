package edu.kit.iti.formal.automation

import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (28.06.17)
 */
class ST0Tests {
    @Test
    fun fbEmbedding1() =
            assertResultST0("fbembedding_1")

    @Test
    fun structEmbedding() =
            assertResultST0("struct_embedding")

    private fun assertResultST0(file: String) {
        var (st, _) = IEC61131Facade.fileResolve(
                CharStreams.fromStream(javaClass.getResourceAsStream("$file.st")))
        val st0exp = IEC61131Facade.file(
                CharStreams.fromStream(javaClass.getResourceAsStream("$file.st0")))

        //val entry = Utils.findProgram(st)!!
        val simplified = SymbExFacade.simplify(st)
        Assertions.assertEquals(IEC61131Facade.print(st0exp, false),
                IEC61131Facade.print(simplified, false))
    }
}
