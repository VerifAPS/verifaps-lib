package edu.kit.iti.formal.automation.web

import edu.kit.iti.formal.automation.FlycheckRunner
import io.ktor.application.Application
import io.ktor.application.call
import io.ktor.application.install
import io.ktor.content.PartData
import io.ktor.content.files
import io.ktor.content.static
import io.ktor.features.*
import io.ktor.gson.gson
import io.ktor.html.respondHtml
import io.ktor.http.HttpHeaders
import io.ktor.http.HttpMethod
import io.ktor.http.HttpStatusCode
import io.ktor.network.tls.certificates.generateCertificate
import io.ktor.request.isMultipart
import io.ktor.request.path
import io.ktor.request.receive
import io.ktor.request.receiveMultipart
import io.ktor.response.respond
import io.ktor.response.respondText
import io.ktor.response.respondWrite
import io.ktor.routing.Routing
import io.ktor.routing.get
import io.ktor.routing.post
import io.ktor.routing.routing
import kotlinx.html.body
import kotlinx.html.h1
import kotlinx.html.li
import kotlinx.html.ul
import org.antlr.v4.runtime.CharStreams
import org.slf4j.event.Level
import java.io.File
import java.io.PrintWriter
import java.io.StringWriter
import java.util.*

//fun main(args: Array<String>): Unit = io.ktor.server.netty.DevelopmentEngine.main(args)

class AuthenticationException : RuntimeException()
class AuthorizationException : RuntimeException()

fun main(args: Array<String>) {
    val file = File("build/temporary.jks")
    if (!file.exists()) {
        file.parentFile.mkdirs()
        generateCertificate(file)
    }
    io.ktor.server.netty.DevelopmentEngine.main(args)
}

fun Application.entry() {
    install(ContentNegotiation) {
        gson {
        }
    }

    install(Compression) {
        gzip {
            priority = 1.0
        }
        deflate {
            priority = 10.0
            minimumSize(1024) // condition
        }
    }

    install(AutoHeadResponse)

    install(CallLogging) {
        level = Level.INFO
        filter { call -> call.request.path().startsWith("/") }
    }

    install(ConditionalHeaders)

    install(CORS) {
        method(HttpMethod.Options)
        method(HttpMethod.Get)
        method(HttpMethod.Post)
        method(HttpMethod.Put)
        method(HttpMethod.Delete)
        method(HttpMethod.Patch)
        header(HttpHeaders.Authorization)
        allowCredentials = true
        anyHost()
    }

    install(DataConversion)

    /*install(HSTS) {
        includeSubDomains = true
    }*/

    /*install(HttpsRedirect) {
        // The port to redirect to. By default 443, the default HTTPS port.
        //sslPort = 8443
        // 301 Moved Permanently, or 302 Found redirect.
        //permanentRedirect = true
    }*/

    install(Routing) {
        flycheck()
    }

    routing {
        // Static feature. Try to access `/static/ktor_logo.svg`
        static("/static") {
            files("static")
        }
        // get("/") { call.respondText("HELLO WORLD!", contentType = ContentType.Text.Plain) }

        get("/html-dsl") {
            call.respondHtml {
                body {
                    h1 { +"HTML" }
                    ul {
                        for (n in 1..10) {
                            li { +"$n" }
                        }
                    }
                }
            }
        }


        get("/json/gson") {
            call.respond(mapOf("hello" to "world"))
        }

        post("/form") {
            val multipart = call.receiveMultipart()
            call.respondWrite {
                if (!call.request.isMultipart()) {
                    appendln("Not a multipart request")
                } else {
                    while (true) {
                        val part = multipart.readPart() ?: break
                        when (part) {
                            is PartData.FormItem ->
                                appendln("FormItem: ${part.name} = ${part.value}")
                            is PartData.FileItem ->
                                appendln("FileItem: ${part.name} -> ${part.originalFileName} of ${part.contentType}")
                        }
                        part.dispose()
                    }
                }
            }
        }

        install(StatusPages) {
            exception<AuthenticationException> { cause ->
                call.respond(HttpStatusCode.Unauthorized)
            }
            exception<AuthorizationException> { cause ->
                call.respond(HttpStatusCode.Forbidden)
            }
        }
    }
}

fun Application.geteta() {

}

fun Application.rvt() {
    routing {
        post("/equal") {
            val aps = RvtApp

        }
    }
}

fun Application.flycheck() {
    routing {
        post("/flycheck") {
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
}