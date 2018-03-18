package edu.kit.iti.formal.automation.smv

import com.xenomachina.argparser.ArgParser
import com.xenomachina.argparser.DefaultHelpFormatter
import com.xenomachina.argparser.default
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import edu.kit.iti.formal.automation.st.ast.TopLevelElements
import edu.kit.iti.formal.smv.NuXMVInvariantsCommand
import edu.kit.iti.formal.smv.NuXMVProcess
import edu.kit.iti.formal.smv.ast.SMVModule
import mu.KLogging
import org.antlr.v4.runtime.CharStreams
import org.apache.commons.io.FileUtils
import java.io.File
import java.io.IOException
import java.nio.charset.Charset


/**
 * This class represents the input arguments for the cli application.
 *
 *
 * @author Alexander Weigl
 */
class RvtArgs(parser: ArgParser) {
    val verbose by parser.flagging("-v", "--verbose", help = "enable verbose mode, set the logger to info")

    val debugMode by parser.flagging("--debug",
            help = "sets the logger to DEBUG level")

    val oldVersion by parser.storing("--old",
            help = "old version of the plc software")
            .default("old.st")

    val newVersion by parser.storing("--new",
            help = "new version of the plc software")
            .default("new.st")

    val disableST0Pipeline by parser.flagging("-D", help = "disable ST0 pipeline")

    val outputSMVOutputName by parser.storing("--to-smv-file",
            help = "name of the smv-module",
            argName = "FILENAME")
            .default("main.smv")

    val outputDirectory by parser.storing("--output", "-o",
            help = "name of the smv-module",
            argName = "FOLDER")
            .default(".")

    val doNotVerify by parser.flagging("--do-not-verify",
            help = "skips the call of nuXmv if set")
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

    val rvtApp = RvtApp(arguments.oldVersion, arguments.newVersion);
    rvtApp.disableSimplifier = arguments.disableST0Pipeline
    rvtApp.outputFolder = File(arguments.outputDirectory)
    rvtApp.outputSmvName = arguments.outputSMVOutputName

    rvtApp.build()
    if (!arguments.doNotVerify)
        rvtApp.verify()
}

class RvtApp(var oldVersionFilename: String,
             var newVersionFilename: String) {
    companion object : KLogging()

    var disableSimplifier: Boolean = false
    var outputFolder = File("output")
    var outputSmvName = "module.smv"
    var nuxmvCommands = NuXMVInvariantsCommand.INVAR
    val nuxmvOutput = "nuxmv.log"

    private var outputSMV: File? = null

    fun build(): RvtApp {
        var st2Pipe = TransformationPipeline(disableSimplifier)
        val oldModule = st2Pipe.run(oldVersionFilename)
        val newModule = st2Pipe.run(newVersionFilename)

        logger.info("Bundling modules $oldVersionFilename with $newVersionFilename")
        val rvt = RegressionVerification(
                newVersion = newModule,
                oldVersion = oldModule)
        rvt.run()

        outputSMV = File(outputFolder, outputSmvName)

        logger.info("Create ouput folder $outputFolder")
        outputFolder.mkdirs()
        outputSMV!!.bufferedWriter().use { fw ->
            rvt.writeTo(fw)
        }
        return this
    }

    fun verify(): Boolean {
        if (outputSMV != null) {
            val mc = NuXMVProcess(outputSMV!!)
            mc.commands = nuxmvCommands.commands as Array<String>
            mc.executablePath = System.getenv().getOrDefault("NUXMV", "nuxmv")
            mc.outputFile = File(outputFolder, nuxmvOutput)
            mc.workingDirectory = outputFolder
            val result = mc.call()
            return result.isVerified
        } else {
            build()
            return verify()
        }
    }

}

/**
 *
 */
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