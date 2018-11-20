package edu.kit.iti.formal.automation.web

import edu.kit.iti.formal.automation.rvt.RvtApsPipeline
import edu.kit.iti.formal.smv.NuXMVOutput
import io.ktor.application.call
import io.ktor.html.respondHtml
import io.ktor.request.header
import io.ktor.request.receive
import io.ktor.response.respond
import io.ktor.routing.Route
import io.ktor.routing.post
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
fun Route.rvt() {
    post("/equal") {
        try {
            val code = call.receive<String>()
            val app = RvtApsPipeline.createRvtForSingleSource(code)
            //TODO app.outputDirectory = File.createTempFile("rvtapp", "", rvtAppFolder)
            app.outputDirectory.mkdirs()
            app.build()
            app.verify()
            val b = app.nuxmvResult
            val r = RvtResponse(app.nuxmvMethod.commands, b!!)
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
