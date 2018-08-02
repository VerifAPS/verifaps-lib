import org.w3c.fetch.*
import kotlin.browser.document
import kotlin.browser.window
import kotlin.js.Promise

/**
 *
 * @author Alexander Weigl
 * @version 1 (02.08.18)
 */
class Service(val url: String) {
    fun get(): Promise<Response> {
        return get(url)
    }

    fun post(body: String): Promise<Response> {
        return post(url, body)
    }
}

fun get(host: dynamic): Promise<Response> {
    return window.fetch(host)
}

fun post(host: dynamic, body: String): Promise<Response> {
    val r = RequestInit()
    r.method = "POST"
    r.cache = RequestCache.NO_CACHE
    r.redirect = RequestRedirect.FOLLOW
    r.body = body
    return window.fetch(host, r)
}

val proto = document.location?.protocol ?: "http"
val hostname = document.location?.hostname ?: "localhost"

val KIT_SERVICE_HOST = "$proto://$hostname:8081"
