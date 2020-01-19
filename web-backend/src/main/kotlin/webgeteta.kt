package edu.kit.iti.formal.automation.web

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParserBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.automation.testtables.print.HTMLTablePrinter
import edu.kit.iti.formal.automation.visitors.Utils
import edu.kit.iti.formal.util.CodeWriter
import io.ktor.application.call
import io.ktor.http.ContentType
import io.ktor.http.HttpStatusCode
import io.ktor.request.receive
import io.ktor.response.respond
import io.ktor.response.respondText
import io.ktor.routing.Route
import io.ktor.routing.get
import io.ktor.routing.post
import kotlinx.html.*
import kotlinx.html.stream.appendHTML
import org.antlr.v4.runtime.CharStreams
import java.io.PrintWriter
import java.io.StringWriter
import java.util.*

data class GetetaExample(val name: String,
                         val code: String,
                         val testtable: String)

object GetetaExamplesRepo {
    val examples: List<GetetaExample>

    init {
        val prefix = "/examples/geteta/"

        fun read(p: String) =
                GetetaExamplesRepo.javaClass.getResourceAsStream(prefix + p)
                        .bufferedReader().useLines { it.joinToString("\n") }

        fun load(name: String): GetetaExample {
            return try {
                val (base, name) = name.split('|')
                val code = read("$base.st")
                val tt = read("$base.tt.txt")
                GetetaExample(name, code, tt)
            } catch (e: Exception) {
                e.printStackTrace()
                GetetaExample(name, "", "")
            }
        }

        val index = read("index")
        examples = index.lines().map { load(it) }
    }
}


fun Route.geteta() {
    get("/geteta/examples") {
        call.respond(GetetaExamplesRepo.examples)
    }

    post("/geteta/generate") {
        val str = context.receive<String>()
        val code = IEC61131Facade.file(CharStreams.fromString(str))
        IEC61131Facade.resolveDataTypes(code)
        val program = Utils.findProgram(code)
        if (program != null) {
            context.respondText(ContentType.Text.Plain) {
                GetetaFacade.generateInterface("tt_" + program.name, scope = program.scope)
            }
            return@post
        }

        context.respondText(ContentType.Text.Plain, HttpStatusCode.InternalServerError) {
            "No program was given. Could not extract interface."
        }
    }

    post("/geteta/render") {
        val table = call.receive<String>()
        try {
            val gtt = GetetaFacade.parseTableDSL(CharStreams.fromString(table))
            call.respondText(ContentType.Text.Html) {
                val backend = StringWriter()
                val stream = CodeWriter(backend)
                try {
                    HTMLTablePrinter(gtt, stream).print()
                } catch (e: Exception) {
                    e.printStackTrace()
                }
                backend.toString()
            }
        } catch (e: Exception) {
            e.printStackTrace()
            call.respondText(ContentType.Text.Plain) { e.message ?: "ERROR" }
        }
    }

    post("/geteta/proof") {

    }
}

