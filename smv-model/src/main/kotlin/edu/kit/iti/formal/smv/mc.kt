package edu.kit.iti.formal.smv

import mu.KLogging
import org.jdom2.input.SAXBuilder
import java.io.File
import java.io.IOException
import java.io.StringReader
import java.util.concurrent.Callable


/**
 * This enum contains possible commands sequences for nuXmv reachability checking.
 * @author Alexander Weigl
 * @version 1 (11.09.17)
 */
enum class NuXMVInvariantsCommand(vararg val commands: String) {
    IC3("read_model", "flatten_hierarchy", "show_vars", "encode_variables",
            "build_boolean_model", "check_invar_ic3", "quit"),
    LTL("read_model", "flatten_hierarchy", "show_vars", "encode_variables",
            "build_model", "check_ltlspec", "quit"),
    INVAR("read_model", "flatten_hierarchy", "show_vars", "encode_variables",
            "build_model", "check_invar", "quit"),
    BMC("read_model", "fKlatten_hierarchy", "show_vars", "encode_variables",
            "build_boolean_model", "check_invar_bmc -a een-sorrensen", "quit")
}

/**
 * This array is a list of commands we need to set for every nuXmv instance.
 * Currently, it sets the TRACE plugin to XML output.
 */
val PREAMBLE = listOf(
        "set default_trace_plugin 6"
)

/**
 * This array is a list of commands we need to set for every nuXmv instance.
 * Currently, it sets the TRACE plugin to XML output.
 */
val POSTAMBLE = listOf(
        "quit"
)

typealias NuXMVOutputParser = (txt: String) -> NuXMVOutput

/**
 * @author Alexander Weigl
 */
class ProcessRunner(val commandLine: Array<String>,
                    val stdin: File,
                    var workingDirectory: File = File("."),
                    var stdoutFile: File = File(workingDirectory, "stdout.log")
) : Callable<String> {

    override fun call(): String {
        val pb = ProcessBuilder(*commandLine)
                //.redirectError(stderrFile)
                .redirectError(ProcessBuilder.Redirect.PIPE)
                .directory(workingDirectory)
                .redirectErrorStream(true)
                .redirectOutput(stdoutFile)
                .redirectInput(stdin)
        val process = pb.start()
        // destroy the sub-process, if java is killed
        Runtime.getRuntime().addShutdownHook(
                Thread { if (process.isAlive) process.destroyForcibly() })
        process.waitFor()

        return stdoutFile.bufferedReader().readText()
    }
}

/**
 *
 * @author Alexander Weigl
 */
class NuXMVProcess(var moduleFile: File) : Callable<NuXMVOutput> {
    var commands: Array<String> = arrayOf("quit")
    var executablePath = "nuXmv"
    var workingDirectory = moduleFile.parentFile
    var outputFile = File(workingDirectory, "nuxmv.log")
    var result: NuXMVOutput? = null
    var outputParser: NuXMVOutputParser = ::parseXmlOutput

    override fun call(): NuXMVOutput {
        workingDirectory.mkdirs()
        val commands = arrayOf(executablePath, "-int", moduleFile.absolutePath)
        try {
            logger.info(commands.joinToString(" "))
            logger.info("Working Directory: {}", workingDirectory)
            logger.info("Result in {}", outputFile)
            val commandFile = createIC3CommandFile()
            val pr = ProcessRunner(commands,
                    commandFile,
                    workingDirectory,
                    outputFile)
            val output = pr.call()
            result = outputParser(output)
            return result!!
        } catch (e: InterruptedException) {
            e.printStackTrace()
        }
        return NuXMVOutput.Error()
    }

    @Throws(IOException::class)
    private fun createIC3CommandFile(): File {
        workingDirectory.mkdirs()
        val f = File(workingDirectory, COMMAND_FILE)
        f.bufferedWriter().use { fw ->
            (PREAMBLE + commands + POSTAMBLE).forEach { fw.write(it + "\n") }
        }
        return f
    }

    companion object : KLogging() {
        val COMMAND_FILE = "commands.xmv"
    }
}

/**
 *
 */
data class CounterExample(
        var type: Int = 0,
        var id: Int = 0,
        var desc: String = "",
        val inputVariables: MutableSet<String> = hashSetOf(),
        val states: MutableList<MutableMap<String, String>> = arrayListOf()
) {
    operator fun get(cycle: Int, name: String): String? =
            try {
                states[cycle][name]
            } catch (e: IndexOutOfBoundsException) {
                null
            }

    val stateSize: Int get() = states.size


    companion object {
        fun load(text: String): CounterExample {
            val ce = CounterExample()
            val saxBuilder = SAXBuilder()
            val doc = saxBuilder.build(StringReader(text));
            val root = doc.rootElement
            ce.type = Integer.parseInt(root.getAttributeValue("type"))
            ce.id = Integer.parseInt(root.getAttributeValue("id"))
            ce.desc = root.getAttributeValue("desc")

            root.getChildren("node").forEach { node ->
                val m = HashMap<String, String>()
                node.getChild("state")?.getChildren("value")?.forEach {
                    m[it.getAttributeValue("variable")] = it.textTrim
                }

                node.getChild("combinatorial")?.getChildren("value")?.forEach {
                    m[it.getAttributeValue("variable")] = it.textTrim
                }

                node.getChild("input")?.getChildren("value")?.forEach {
                    ce.inputVariables.add(it.getAttributeValue("variable"))
                    m[it.getAttributeValue("variable")] = it.textTrim
                }
                ce.states += m
            }

            return ce
        }
    }
}

/**
 * Represents an output of a nuxmv run.
 * @author Alexander Weigl
 * @version 2
 */
sealed class NuXMVOutput {
    object Verified : NuXMVOutput()
    class Error(val errors: List<String> = arrayListOf()) : NuXMVOutput()
    class NotVerified(val counterExample: CounterExample) : NuXMVOutput()
}

/**
 *
 */
fun parseXmlOutput(text: String): NuXMVOutput {
    val lines = text.split('\n')
    val errorLinePredicate = { it: String ->
        //empirical
        it.contains("error")
                || it.contains("syntax error")
                || it.contains("TYPE ERROR")
                || it.contains("undefined")
                || it.contains("too few actual parameters")
    }

    if (errorLinePredicate(text)) {
        val errors = lines.filter(errorLinePredicate)
        return NuXMVOutput.Error(errors)
    }

    val idxCex = lines.indexOfFirst {
        it.startsWith("<counter-example")
    }
    if (idxCex != -1) {
        val closing = lines.lastIndexOf("</counter-example>")
        val xml = lines.slice(idxCex..closing)
                .joinToString("\n")
        return NuXMVOutput.NotVerified(CounterExample.load(xml))
    }
    return NuXMVOutput.Verified
}

/**
 */
fun getNuXmvVersion(command: String): String {
    val builder = ProcessBuilder(command)
            .redirectErrorStream(true)
    val process = builder.start()
    //val stdin = process.outputStream
    val stdout = process.inputStream

    //stdin.bufferedWriter().write("quit\n")
    val lines = stdout.bufferedReader().readLines()
    return getNuXmvVersion(lines)
}

fun getNuXmvVersion(lines: List<String>): String {
    //*** This is nuXmv 1.1.1 (compiled on Wed Jun  1 10:18:42 2016)
    val l = lines[0]
    return l.substringAfter("This is").substringBefore('(')
}

