import org.gradle.api.DefaultTask
import org.gradle.api.file.RegularFileProperty
import org.gradle.api.tasks.InputFile
import org.gradle.api.tasks.OutputFile
import org.gradle.api.tasks.TaskAction
import org.jetbrains.kotlin.org.apache.commons.compress.archivers.sevenz.SevenZFile
import java.nio.channels.FileChannel
import kotlin.io.path.createDirectories
import kotlin.io.path.outputStream

/**
 *
 * @author Alexander Weigl
 * @version 1 (7/26/25)
 */
@Suppress("unused")
abstract class Extract7z : DefaultTask() {
    @get:InputFile
    abstract val input: RegularFileProperty

    @get:OutputFile
    abstract val output: RegularFileProperty

    @TaskAction
    fun uncompress() {
        val channel = FileChannel.open(input.get().asFile.toPath())
        val file = SevenZFile.builder().setSeekableByteChannel(channel).get()
        val base = output.get().asFile.toPath()
        file.use {
            it.entries.forEach { entry ->
                if (entry.isDirectory) {
                    val folder = base.resolve(entry.name)
                    folder.createDirectories()
                } else {
                    val outputFile = base.resolve(entry.name)
                    outputFile.parent.createDirectories()
                    outputFile.outputStream().use {
                        file.getInputStream(entry).copyTo(it)
                    }
                }
            }
        }
    }
}