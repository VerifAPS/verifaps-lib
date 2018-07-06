package edu.kit.iti.formal.automation.web

import edu.kit.iti.formal.automation.FlycheckRunner
import edu.kit.iti.formal.automation.rvt.RvtApp
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
        basics()
        geteta()
        rvt()
    }

    routing {
        // Static feature. Try to access `/static/ktor_logo.svg`
        static("/static") {
            files("static")
        }
        // get("/") { call.respondText("HELLO WORLD!", contentType = ContentType.Text.Plain) }

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


data class RpcResponse(
        /** A String specifying the version of the JSON-RPC protocol. MUST be exactly "2.0".*/
        val jsonrpc: String = "2.0",

        /**
         * This member is REQUIRED on success.
         * This member MUST NOT exist if there was an error invoking the method.
         * The value of this member is determined by the method invoked on the Server.
         */
        val result: Any?,

        /**
         * This member is REQUIRED on error.
         * This member MUST NOT exist if there was no error triggered during invocation.
         * The value for this member MUST be an Object as defined in section 5.1.
         */
        val error: Any?,
        /** This member is REQUIRED.
         * It MUST be the same as the value of the id member in the Request Object.
         * If there was an error in detecting the id in the Request object(e.g. Parse error/Invalid Request), it MUST be Null.
         * Either the result member or error member MUST be included, but both members MUST NOT be included.
         */
        val id: Int
)

data class JsonError(
        /** A Number that indicates the error type that occurred. This MUST be an integer.*/
        val code: Int,
        /** A String providing a short description of the error. The message SHOULD be limited to a concise single sentence. */
        val message: String,
        /** A Primitive or Structured value that contains additional information about the error.
         * This may be omitted.
         * The value of this member is defined by the Server (e.g. detailed error information,
         *nested errors etc.).
         */
        val data: Any?
)


