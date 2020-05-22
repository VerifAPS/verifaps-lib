package edu.kit.iti.formal.automation

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import org.antlr.v4.runtime.CharStreams
import java.io.OutputStreamWriter


object Xml2TxtApp {
    @JvmStatic
    fun main(args: Array<String>) = Xml2Txt().main(args)
}

class Xml2Txt : CliktCommand() {
    val input by argument(name = "XML", help = "Files to read").file()

    val simplify by option().flag()

    val noSfc by option("--translate-sfc").flag()

    val noFbd by option("--translate-fbd").flag()

    val preOutput by option("-po", "--pre-output", help = "File to write").file()

    val output by option("-o", "--output", help = "File to write").file()

    override fun run() {
        IEC61131Facade.useOldSfcTranslator = true

        //val base = if (includeBuiltIn) BuiltinLoader.loadDefault() else PouElements()
        val text = IECXMLFacade.extractPLCOpenXml(input)
        val out = output?.bufferedWriter() ?: OutputStreamWriter(System.out)

        if (!noSfc && !noFbd) {
            out.write(text)
            return
        }

        preOutput?.writeText(text)

        val pous = IEC61131Facade.file(CharStreams.fromString(text))
        pous.addAll(BuiltinLoader.loadDefault())
        IEC61131Facade.resolveDataTypes(pous)

        if (noSfc) IEC61131Facade.translateSfcToSt(pous)
        if (noFbd) IEC61131Facade.translateFbd(pous)
        if (simplify) {
            val p = SymbExFacade.simplify(pous)
            IEC61131Facade.printTo(out, p, true)
        } else {
            IEC61131Facade.printTo(out, pous, true)
        }
        out.close()
    }
}