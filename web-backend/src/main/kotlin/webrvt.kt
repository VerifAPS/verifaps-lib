package edu.kit.iti.formal.automation.web

import edu.kit.iti.formal.automation.rvt.RvtApp
import edu.kit.iti.formal.smv.NuXMVOutput
import io.ktor.application.Application
import io.ktor.application.call
import io.ktor.html.respondHtml
import io.ktor.request.header
import io.ktor.request.receive
import io.ktor.response.respond
import io.ktor.routing.post
import io.ktor.routing.routing
import java.io.File

/**
 *
 * @author Alexander Weigl
 * @version 1 (06.07.18)
 */


data class RvtResponse(
        val commands: Array<out String>,
        val b: NuXMVOutput
)

val rvtAppFolder = File("rvtapps")
fun Application.rvt() {
    routing {
        post("/equal") {
            try {
                val code = call.receive<String>()
                val app = RvtApp.createRvtForSingleSource(code)
                app.outputFolder = File.createTempFile("rvtapp", "", rvtAppFolder)
                app.outputFolder.mkdirs()
                app.build()
                val b = app.verify()
                val r = RvtResponse(app.nuxmvCommands.commands, b)
                if (call.request.header("Content-Type") == "application/json") {
                    call.respond(r)
                } else {
                    call.respondHtml { }
                }
            } catch (e: Exception) {
                call.respond(e)
            }
        }
    }
}
