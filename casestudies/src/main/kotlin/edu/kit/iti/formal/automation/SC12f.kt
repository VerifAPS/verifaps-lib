package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.sfclang.SFC2ST
import edu.kit.iti.formal.automation.st.ast.*
import org.jdom2.JDOMException
import java.io.File
import java.io.IOException

/**
 * @author Alexander Weigl
 * @version 1 (25.02.18)
 */
object Sc12f {
    private val typeDecls = TypeDeclarations()

    @Throws(JDOMException::class, IOException::class)
    @JvmStatic
    fun main(args: Array<String>) {
        val start = System.currentTimeMillis()
        val f = "/home/weigl/Scenario12f.xml"
        val tles = IECXMLFacade.readPLCOpenXml(f)

        System.out.printf("// Reading Time: %d ms%n", System.currentTimeMillis() - start)

        File("SC12f.iec61131").writer().use {
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

        tles.add(0, typeDecls);
        File("SC12f.st").writer().use {
            it.write(IEC61131Facade.print(tles))
        }
        println(File("SC12f.st").absolutePath + " written!")

        //IEC61131Facade.resolveDataTypes(tles)

        val stles = SymbExFacade.simplify(tles)
        File("SC12f.st0").writer().use {
            it.write(IEC61131Facade.print(stles))
        }
        println(File("SC12f.st0").absolutePath + " written!")


        val smv = SymbExFacade.evaluateProgram(stles.get(1) as PouElements)
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
            val ss = SFC2ST("",
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
            val ss = SFC2ST("",
                    pd.sfcBody?.networks!![0],
                    pd.scope
            )
            pd.stBody = ss.get()
            typeDecls.add(ss.enumDecl)
        }
        translate(pd.name, pd.scope, pd.actions)
    }
}
