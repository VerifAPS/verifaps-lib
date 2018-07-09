package edu.kit.iti.formal.automation.rvt

import com.xenomachina.argparser.ArgParser
import com.xenomachina.argparser.DefaultHelpFormatter
import com.xenomachina.argparser.default
import edu.kit.iti.formal.automation.Console
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import edu.kit.iti.formal.automation.st.ast.PouElements
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration
import edu.kit.iti.formal.smv.NuXMVInvariantsCommand
import edu.kit.iti.formal.smv.NuXMVOutput
import edu.kit.iti.formal.smv.NuXMVProcess
import edu.kit.iti.formal.smv.ast.SMVModule
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.apache.commons.io.FileUtils
import java.io.File
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

    val rvtApp = RvtApp(
            TransformationPipeline.create(arguments.oldVersion, arguments.disableST0Pipeline),
            TransformationPipeline.create(arguments.newVersion, arguments.disableST0Pipeline))

    rvtApp.outputFolder = File(arguments.outputDirectory)
    rvtApp.outputSmvName = arguments.outputSMVOutputName

    rvtApp.build()
    if (!arguments.doNotVerify)
        rvtApp.verify()
}

class RvtApp(var oldVersion: () -> SMVModule,
             var newVersion: () -> SMVModule) {
    var disableSimplifier: Boolean = false
    var outputFolder = File("output")
    var outputSmvName = "module.smv"
    var nuxmvCommands = NuXMVInvariantsCommand.INVAR
    val nuxmvOutput = "nuxmv.log"

    private var outputSMV: File? = null

    fun build(): RvtApp {
        val oldModule = oldVersion()
        val newModule = newVersion()

        Console.info("Bundling modules $oldVersion with $newVersion")
        val rvt = RegressionVerification(
                newVersion = newModule,
                oldVersion = oldModule)
        rvt.run()

        outputSMV = File(outputFolder, outputSmvName)

        Console.info("Create ouput folder $outputFolder")
        outputFolder.mkdirs()
        outputSMV!!.bufferedWriter().use { fw ->
            rvt.writeTo(fw)
        }
        return this
    }

    fun verify(): NuXMVOutput {
        if (outputSMV != null) {
            val mc = NuXMVProcess(outputSMV!!)
            mc.commands = nuxmvCommands.commands as Array<String>
            mc.executablePath = System.getenv().getOrDefault("NUXMV", "nuxmv")
            mc.outputFile = File(outputFolder, nuxmvOutput)
            mc.workingDirectory = outputFolder
            return mc.call()
        } else {
            build()
            return verify()
        }
    }

    companion object {
        /**
         * Finds the first two programs in the given code and creates an [RvtApp]
         * with the other elements.
         */
        fun createRvtForSingleSource(code: String): RvtApp {
            val elements = IEC61131Facade.file(CharStreams.fromString(code))
            elements.addAll(BuiltinLoader.loadDefault())
            val (fst, snd) = separatePrograms(elements)

            val aps = RvtApp(
                    oldVersion = { TransformationPipeline(false).run(fst) },
                    newVersion = { TransformationPipeline(false).run(snd) })

            return aps
        }
    }
}

fun separatePrograms(elements: PouElements): Pair<PouElements, PouElements> {
    val (fst, snd) = elements.filter { it is ProgramDeclaration }
    val copy = PouElements(elements)
    copy.removeAll { it is ProgramDeclaration }
    val a = PouElements(copy);a.add(fst)
    val b = PouElements(copy);b.add(snd)
    return a to b
}

/**
 *
 */
class TransformationPipeline(var diableST0: Boolean = false) {
    companion object {
        fun create(filename: String, disableSimp: Boolean) = { TransformationPipeline(disableSimp).run(filename) }
        fun create(input: CharStream, disableSimp: Boolean) = { TransformationPipeline(disableSimp).run(input) }
    }

    fun run(filename: String): SMVModule {
        var elements: PouElements =
                if (filename.endsWith(".xml")) {
                    IECXMLFacade.readPLCOpenXml(filename)
                } else {
                    val content = FileUtils.readFileToString(File(filename), Charset.defaultCharset())
                    IEC61131Facade.file(CharStreams.fromString(content))
                }
        return run(elements)
    }

    fun run(filename: CharStream) = run(IEC61131Facade.file(filename))

    fun run(elements: PouElements): SMVModule {
        IEC61131Facade.resolveDataTypes(elements)
        return SymbExFacade.evaluateProgram(elements, diableST0)
    }

}
