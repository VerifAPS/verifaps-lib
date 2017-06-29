package edu.kit.iti.formal.automation.rvt

import com.xenomachina.argparser.ArgParser
import com.xenomachina.argparser.DefaultHelpFormatter
import com.xenomachina.argparser.default
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import edu.kit.iti.formal.automation.st.ast.TopLevelElements
import edu.kit.iti.formal.smv.ast.SMVModuleImpl
import org.apache.commons.io.FileUtils
import java.io.File
import java.io.IOException
import java.nio.charset.Charset


class RvtArgs(parser: ArgParser) {
    val verbose by parser.flagging("-v", "--verbose", help = "enable verbose mode")
    val debugMode by parser.flagging("--debug", help = "enable debugging")
    val oldVersion by parser.storing("old version of the plc software").default("old.st")
    val newVersion by parser.storing("new version of the plc software").default("new.st")
    val disableST0Pipeline by parser.flagging("-D", help = "disable ST0 pipeline")
    val mainModule by parser.storing("name of the main module")
}

fun main(args: Array<String>) {
    val hf = DefaultHelpFormatter()
    val parser = ArgParser(args, helpFormatter = hf)
    val arguments = RvtArgs(parser)

    var st2Pipe = TransformationPipeline(arguments.debugMode,
            arguments.disableST0Pipeline)

}

class TransformationPipeline(var debug: Boolean = false,
                             var diableST0: Boolean = false) {
    fun run(filename: String): SMVModuleImpl {
        try {
            var elements: TopLevelElements;
            if (filename.endsWith(".xml")) {
                elements = IECXMLFacade.readPLCOpenXml(filename)
            } else {
                val content = FileUtils.readFileToString(File(filename), Charset.defaultCharset())
                elements = IEC61131Facade.file(content)
            }

            if (!diableST0)
                elements = SymbExFacade.simplify(elements)

            SymbExFacade.evaluateProgram(elements);
        } catch (e: IOException) {
            e.printStackTrace()
            throw e
        }
    }
}