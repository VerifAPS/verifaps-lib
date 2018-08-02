package edu.kit.iti.formal.automation.web

import com.typesafe.config.ConfigFactory
import edu.kit.iti.formal.automation.FlycheckRunner
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.visitors.Utils
import io.github.config4k.extract
import io.ktor.application.call
import io.ktor.request.receive
import io.ktor.response.respond
import io.ktor.response.respondText
import io.ktor.routing.Route
import io.ktor.routing.post
import org.antlr.v4.runtime.CharStreams
import java.io.PrintWriter
import java.io.StringWriter
import java.util.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (06.07.18)
 */
fun Route.basics() {
    post("/signature") {
        val code = call.receive<String>()
        val ast = IEC61131Facade.file(CharStreams.fromString(code))
        IEC61131Facade.resolveDataTypes(ast)
        val program = Utils.findProgram(ast)
        if (program == null) {
            call.respond(JsonError(1, "No program found in the given stCode.", null))
        } else {
            call.respond(
                    program.scope.map {
                        mapOf("id" to it.name,
                                "dataType" to it.dataType,
                                "init" to it.initValue,
                                "posStart" to it.startPosition,
                                "posStop" to it.endPosition)
                    }
            )
        }
    }

    post("/checksyntax") {
        val code = call.receive<String>()
        val runner = FlycheckRunner(
                Collections.singletonList(CharStreams.fromString(code))
        )
        try {
            runner.run()
            call.respond(runner.messages)
        } catch (e: Exception) {
            call.respondText {
                val s = PrintWriter(StringWriter())
                e.printStackTrace(s)
                s.toString()
            }
        }
    }
}


sealed class CodeExample {
    abstract val name: String
    abstract val description: String
    abstract val exampleType: String
    abstract val stCode: String
}

data class SimpleCodeExample(
        override var name: String,
        override var description: String,
        override var stCode: String
) : CodeExample() {
    override val exampleType: String = "simple"
}

data class GetetaExample(
        override var name: String,
        override var description: String,
        override var stCode: String,
        var testtable: String) : CodeExample() {
    override val exampleType: String = "testtable"
}

data class RegressionExample(override var name: String,
                             override var description: String,
                             override var stCode: String)
    : CodeExample() {
    override val exampleType: String = "simple"
}

object ExamplesRepo {
    val examples: List<CodeExample>
    val prefix = "/examples/"

    init {
        examples = readIndex()
                .map { (n, t) -> load(n, t) }
                .filter { it != null }
                .map { it!! }
    }

    fun readIndex() =
            ExamplesRepo.javaClass.getResourceAsStream(prefix + "index")
                    .bufferedReader().readLines().map {
                        val (name, type) = it.split("|")
                        name to type
                    }

    fun read(p: String) =
            ExamplesRepo.javaClass.getResourceAsStream(prefix + p)
                    .bufferedReader().useLines { it.joinToString("\n") }

    fun load(name: String, type: String): CodeExample? {
        return try {
            val config = ConfigFactory.parseResources("$prefix/$name.conf")

            when (type) {
                "rv" -> config.extract<RegressionExample>("")
                "tt" -> config.extract<GetetaExample>("")
                "simp" -> config.extract<SimpleCodeExample>("")
                else -> null
            }
        } catch (e: Exception) {
            e.printStackTrace()
            null
        }
    }
}
