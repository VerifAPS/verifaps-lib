package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.sfclang.SFC2ST
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.findProgram
import org.antlr.v4.runtime.CharStreams
import java.io.File

/**
 * @author Alexander Weigl
 * @version 1 (25.02.18)
 */
object SC11_rev {
    private val typeDecls = TypeDeclarations()

    @JvmStatic
    fun main(args: Array<String>) {
        val start = System.currentTimeMillis()

        val f = "/home/weigl/Documents/IMPROVE/Papiere/at2018/data/case3/Scenario11_Final_rev.xml"
        val code = IECXMLFacade.extractPLCOpenXml(f)
        val tles = IEC61131Facade.file(CharStreams.fromString(code))

        System.out.printf("// Reading Time: %d ms%n", System.currentTimeMillis() - start)

        File("SC11_rev.iec61131").writer().use {
            it.write(IEC61131Facade.print(tles))
        }

        for (tle in tles) {
            if (tle is ProgramDeclaration) {
                removeShittySFCVars(tle.scope)
                translate(tle)
            }
            if (tle is FunctionBlockDeclaration) {
                translate(tle)
                removeShittySFCVars(tle.scope)
            }
        }

        tles.add(0, typeDecls)
        tles.addAll(IEC61131Facade.file(File("ton.st").absoluteFile))
        IEC61131Facade.resolveDataTypes(tles)
        File("SC11_rev.st").writer().use {
            it.write(IEC61131Facade.print(tles))
        }
        println(File("SC11_rev.st").absolutePath + " written!")


        val stles = SymbExFacade.simplify(tles)
        // we need to trick with the input/output variables
        findProgram(tles)?.scope?.forEach {
            if (it.name.startsWith("Actuator_"))
                it.type = it.type or VariableDeclaration.OUTPUT
            if (it.name.startsWith("Sensor_"))
                it.type = it.type or VariableDeclaration.INPUT
        }

        File("SC11_rev.st0").writer().use {
            it.write(IEC61131Facade.print(stles, true))
        }
        println(File("SC11_rev.st0").absolutePath + " written!")


        val smv = SymbExFacade.evaluateProgram(stles)
        File("SC12f.smv").writer().use {
            it.write(smv.toString())
        }
        println(File("SC12f.smv").absolutePath + " written!")

        val stop = System.currentTimeMillis()
        System.out.printf("// Time: %d ms%n", stop - start)
    }

    private fun removeShittySFCVars(scope: Scope) {
        val s = arrayOf("SFCCurrentStep", "SFCEnableLimit", "SFCError",
                "SFCErrorAnalyzation", "SFCErrorAnalyzationTable", "SFCErrorPOU",
                "SFCErrorStep", "SFCInit", "SFCPause", "SFCQuitError", "SFCTip",
                "SFCTipMode", "SFCTrans")
        s.forEach { scope.asMap().remove(it) }
    }

    private fun translate(fbd: FunctionBlockDeclaration) {
        if (fbd.sfcBody != null) {
            val ss = SFC2ST(fbd.name,
                    fbd.sfcBody?.networks!![0],
                    fbd.scope
            )
            fbd.stBody = ss.get()
            typeDecls.add(ss.enumDecl)
        }
        translate(fbd.name, fbd.scope, fbd.actions)
    }

    private fun translate(name: String, scope: Scope, actions: Collection<ActionDeclaration>) {
        actions.forEach { a -> translate(name, scope, a) }
    }

    private fun translate(name: String, scope: Scope, a: ActionDeclaration) {
        if (a.sfcBody != null) {
            val ss = SFC2ST(name + "__" + a.name,
                    a.sfcBody!!.networks[0],
                    scope
            )
            a.stBody = ss.get()
            typeDecls.add(ss.enumDecl)
        }
    }

    private fun translate(pd: ProgramDeclaration) {
        if (pd.sfcBody != null) {
            val ss = SFC2ST(pd.name,
                    pd.sfcBody?.networks!![0],
                    pd.scope
            )
            pd.stBody = ss.get()
            typeDecls.add(ss.enumDecl)
        }
        translate(pd.name, pd.scope, pd.actions)

    }
}
