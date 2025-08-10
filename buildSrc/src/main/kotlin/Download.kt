import org.gradle.api.DefaultTask
import org.gradle.api.provider.Property
import org.gradle.api.tasks.Input
import org.gradle.api.tasks.Optional
import org.gradle.api.tasks.OutputFile
import org.gradle.api.tasks.TaskAction
import java.io.File
import java.net.URI
import java.security.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (7/26/25)
 */
abstract class Download : DefaultTask() {
    @get:Input
    abstract val source: Property<URI>

    @get:Input
    @get:Optional
    abstract val checksumSha256Url: Property<URI>

    @get:OutputFile
    abstract val outputFile: Property<File>

    @TaskAction
    fun action() {
        val asFile = outputFile.get()
        val md = MessageDigest.getInstance("SHA-256")

        asFile.parentFile.mkdirs()
        asFile.outputStream().buffered().use { writer ->
            DigestInputStream(source.get().toURL().openStream().buffered(), md).use { dis ->
                dis.copyTo(writer)
            }
        }

        val sha256 = buildString {
            md.digest().forEach {
                val hex = it.toString(16)
                if (hex.length == 1) append('0')
                append(hex)
            }
        }
        println(sha256)

        if (checksumSha256Url.isPresent) {
            val internetSha256 = checksumSha256Url.get().toURL().readText()
            println(internetSha256)
        }
    }
}