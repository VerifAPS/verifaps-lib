package edu.kit.iti.formal.automation.rvt

import com.xenomachina.argparser.ArgParser
import com.xenomachina.argparser.DefaultHelpFormatter
import com.xenomachina.argparser.default
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import edu.kit.iti.formal.automation.st.ast.TopLevelElements
import edu.kit.iti.formal.smv.ast.SMVModule
import mu.KLogging
import org.antlr.v4.runtime.CharStreams
import org.apache.commons.io.FileUtils
import java.io.File
import java.io.IOException
import java.nio.charset.Charset


class RvtArgs(parser: ArgParser) {
    val verbose by parser.flagging("-v", "--verbose", help = "enable verbose mode")
    val debugMode by parser.flagging("--debug", help = "enable debugging")
    val oldVersion by parser.storing("--old", help = "old version of the plc software").default("old.st")
    val newVersion by parser.storing("--new", help = "new version of the plc software").default("new.st")
    val disableST0Pipeline by parser.flagging("-D", help = "disable ST0 pipeline")

    val outputSMVOutputName by parser.storing("--to-smv-file", help = "name of the smv-module", argName = "FILENAME")
            .default("main.smv")

    val outputDirectory by parser.storing("--output", "-o", help = "name of the smv-module", argName = "FOLDER")
            .default(".")
}

/**
 * Entry point for Regression Verification
 *
 * @param args
 */
fun main(args: Array<String>) {
    val hf = DefaultHelpFormatter()
    val parser = ArgParser(args, helpFormatter = hf)
    val arguments = RvtArgs(parser)

    var st2Pipe = TransformationPipeline(arguments.disableST0Pipeline)

    val oldModule = st2Pipe.run(arguments.oldVersion)
    val newModule = st2Pipe.run(arguments.newVersion)

    val rvt = RegressionVerification(
            newVersion = newModule,
            oldVersion = oldModule)
    rvt.run()

    val outputFolder = File(arguments.outputDirectory)
    val outputSMV = File(outputFolder, arguments.outputSMVOutputName)

    outputFolder.mkdirs()
    val writer = outputSMV.bufferedWriter()
    rvt.writeTo(writer)
    writer.close()
}

class TransformationPipeline(var diableST0: Boolean = false) {
    companion object : KLogging()

    fun run(filename: String): SMVModule {
        try {
            var elements: TopLevelElements;
            if (filename.endsWith(".xml")) {
                elements = IECXMLFacade.readPLCOpenXml(filename)
            } else {
                val content = FileUtils.readFileToString(File(filename), Charset.defaultCharset())
                elements = IEC61131Facade.file(CharStreams.fromString(content))
            }

            if (!diableST0) {
                logger.info("running tranformation to ST0")
                elements = SymbExFacade.simplify(elements)
            }
            return SymbExFacade.evaluateProgram(elements)
        } catch (e: IOException) {
            e.printStackTrace()
            throw e
        }

    }
}