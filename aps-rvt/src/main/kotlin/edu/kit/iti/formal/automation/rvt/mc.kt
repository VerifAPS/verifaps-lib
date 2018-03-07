package edu.kit.iti.formal.automation.rvt

import mu.KLogging
import java.io.File
import java.io.IOException
import java.util.concurrent.Callable
import javax.xml.bind.JAXBContext
import javax.xml.bind.annotation.*


/**
 * This enum contains possible commands sequences for nuXmv reachability checking.
 * @author Alexander Weigl
 * @version 1 (11.09.17)
 */
enum class NuXMVCommand(vararg val commands: String) {
    IC3("read_model", "flatten_hierarchy", "show_vars", "encode_variables",
            "build_boolean_model", "check_invar_ic3", "quit"),
    LTL("read_model", "flatten_hierarchy", "show_vars", "encode_variables",
            "build_model", "check_ltlspec", "quit"),
    INVAR("read_model", "flatten_hierarchy", "show_vars", "encode_variables",
            "build_model", "check_invar", "quit"),
    BMC("read_model", "flatten_hierarchy", "show_vars", "encode_variables",
            "build_boolean_model", "check_invar_bmc -a een-sorrensen", "quit")
}

/**
 * This array is a list of commands we need to set for every nuXmv instance.
 * Currently, it sets the TRACE plugin to XML output.
 *
 *
 */
val PREAMBLE = listOf(
        "set default_trace_plugin 6"
)

/**
 * @author Alexander Weigl
 */
class ProcessRunner(val commandLine: Array<String>,
                    val stdin: File)
    : Callable<String> {

    var stdoutFile = File("stdout.log")
    //var stderrFile = File("stderr.log")
    var workingDirectory = File(".")

    override fun call(): String {
        val pb = ProcessBuilder(*commandLine)
                //.redirectError(stderrFile)
                .redirectError(ProcessBuilder.Redirect.PIPE)
                .directory(workingDirectory)
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

inline fun println(fmt: String, vararg obj: Any?) {
    System.out.format(fmt, *obj)
}

/**
 *
 * @author Alexander Weigl
 */
class NuXMVProcess(var moduleFile: File) : Callable<Boolean> {

    var commands: Array<String> = arrayOf("quit")
    var executablePath = "nuXmv"
    var workingDirectory = moduleFile.parentFile
    var outputFile = File("nuxmv.log")
    var isVerified: Boolean = false
        get() = if (result != null) result!!.isVerified else false

    private var result: NuXMVOutput? = null


    override fun call(): Boolean {
        workingDirectory.mkdirs()
        val commands = arrayOf(executablePath, "-int", moduleFile.absolutePath)
        try {
            logger.info(commands.joinToString(" "))
            logger.info("Working Directory: {}", workingDirectory)
            logger.info("Result in {}", outputFile)
            val commandFile = createIC3CommandFile()
            val pr = ProcessRunner(commands, commandFile)
            pr.stdoutFile = outputFile
            val output = pr.call()
            result = parseOutput(output)
        } catch (e: InterruptedException) {
            e.printStackTrace()
        }
        return isVerified
    }

    @Throws(IOException::class)
    private fun createIC3CommandFile(): File {
        workingDirectory.mkdirs()
        val f = File(workingDirectory, COMMAND_FILE)
        f.bufferedWriter().use { fw ->
            PREAMBLE.forEach { fw.write(it + "\n") }
            commands.forEach { fw.write(it + "\n") }
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
@XmlRootElement(name = "counter-example")
@XmlAccessorType(XmlAccessType.FIELD)
@XmlType
class CounterExample {
    @field:XmlAttribute
    var type: String? = null

    @field:XmlAttribute
    var id: String? = null

    @field:XmlAttribute
    var desc: String? = null

    @field:XmlElements(XmlElement(name = "node"))
    var nodes: List<Node> = arrayListOf()

    @XmlType
    @XmlAccessorType(XmlAccessType.FIELD)

    class Node {
        @field:XmlElement
        var state: Values = Values()

        @field:XmlElement
        var input: Values = Values()

        @field:XmlElement
        var combinatorial: Values = Values()

        override fun toString(): String {
            return "Node(state=$state, input=$input, combinatorial=$combinatorial)"
        }
    }

    @XmlType
    @XmlAccessorType(XmlAccessType.FIELD)

    class Values {
        @field:XmlAttribute
        var id: Integer? = null

        @field:XmlElements(XmlElement(name = "value"))
        var values = arrayListOf<Value>()

        override fun toString(): String {
            return "Values(id=$id, values=$values)"
        }
    }

    @XmlType
    @XmlAccessorType(XmlAccessType.FIELD)

    class Value {
        @field:XmlAttribute
        var variable: String = ""

        @field:XmlValue
        var value: String = ""

        override fun toString(): String {
            return "Value(variable='$variable', value='$value')"
        }
    }

    override fun toString(): String {
        return "CounterExample(type=$type, id=$id, desc=$desc, nodes=$nodes)"
    }

    companion object {
        fun load(xml: String): CounterExample {
            val ctx = JAXBContext.newInstance(CounterExample::class.java)
            val um = ctx.createUnmarshaller()
            val cex = um.unmarshal(xml.reader())
            return cex as CounterExample
        }
    }
}

/**
 * @author Alexander Weigl
 */
class NuXMVOutput(
        val errors: List<String> = arrayListOf(),
        val counterExample: CounterExample? = null
) {
    val hasErrors: Boolean
        get() = errors.isNotEmpty()
    val isVerified: Boolean
        get() = counterExample == null
}

fun parseOutput(text: String): NuXMVOutput {
    val lines = text.split('\n')

    val predError = { it: String ->
        //empirical
        it.contains("error")
                || it.contains("TYPE ERROR")
                || it.contains("undefined")
    }

    if (predError(text)) {
        val errors =
                lines.filter(predError)
        return NuXMVOutput(errors)
    }

    val idxCex = lines.indexOfFirst {
        it.startsWith("<counter-example")
    }
    if (idxCex != -1) {
        val closing = lines.lastIndexOf("</counter-example>")
        val xml = lines.slice(idxCex..closing)
                .joinToString("\n")
        return NuXMVOutput(counterExample = CounterExample.load(xml))
    }
    return NuXMVOutput()
}