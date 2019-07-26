package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration
import edu.kit.iti.formal.automation.st.ast.SFCNetwork
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (20.06.19)
 */
class TranslationSfcToStPipelineTest {
    val file = "single_sfc2st_tests.st"

    @Test
    fun simple1() {
        val (scope, network) = readSfc(file, "simple1")
        val t = TranslationSfcToStPipeline(network,
                name = "simple1", scope = scope, maxNeededTokens = TokenAmount.Bounded(1), sfcFlags = false)
        val s = t.call()
        val fbd = FunctionBlockDeclaration("TEST", scope, s)
        println(IEC61131Facade.print(fbd))
    }

    @Test
    fun simple1_reset() {
        val (scope, network) = readSfc(file, "simple1")
        val t = TranslationSfcToStPipeline(network,
                name = "simple1", scope = scope, maxNeededTokens = TokenAmount.Bounded(1),
                sfcFlags = true)
        val s = t.call()
        val fbd = FunctionBlockDeclaration("TEST", scope, s)
        println(IEC61131Facade.print(fbd))
    }

    @Test
    fun simpleOnlyActions() {
        val (scope, network) = readSfc(file, "simpleOnlyActions")
        val t = TranslationSfcToStPipeline(network,
                name = "simpleOnlyActions", scope = scope, maxNeededTokens = TokenAmount.Bounded(1),
                sfcFlags = false)
        val s = t.call()
        val fbd = FunctionBlockDeclaration("TEST", scope, s)
        println(IEC61131Facade.print(fbd))
    }

    @Test
    fun simpleOnlyActions_reset() {
        val (scope, network) = readSfc(file, "simpleOnlyActions")
        val t = TranslationSfcToStPipeline(network,
                name = "simpleOnlyActions", scope = scope, maxNeededTokens = TokenAmount.Bounded(1),
                sfcFlags = true)
        val s = t.call()
        val fbd = FunctionBlockDeclaration("TEST", scope, s)
        println(IEC61131Facade.print(fbd))
    }


    private fun readSfc(s: String, fbdName: String): Pair<Scope, SFCNetwork> {
        val res = javaClass.getResourceAsStream(s)
        assertNotNull(res)
        val pous = IEC61131Facade.file(res).also {
            it.addAll(BuiltinLoader.loadDefault())
            IEC61131Facade.resolveDataTypes(it)
        }
        val fbd = pous.find { it.name == fbdName } as? FunctionBlockDeclaration
        assertNotNull(fbd)
        val sfc = fbd?.sfcBody?.networks?.first()
        assertNotNull(sfc)
        return fbd?.scope!! to sfc!!
    }
}