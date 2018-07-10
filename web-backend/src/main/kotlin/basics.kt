package edu.kit.iti.formal.automation.web

import edu.kit.iti.formal.automation.FlycheckRunner
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.visitors.Utils
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
            call.respond(JsonError(1, "No program found in the given code.", null))
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
