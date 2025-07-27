import org.gradle.api.DefaultTask
import org.gradle.api.file.RegularFileProperty
import org.gradle.api.tasks.InputFile
import org.gradle.api.tasks.OutputFile
import org.gradle.api.tasks.TaskAction
import org.jetbrains.kotlin.org.apache.commons.compress.compressors.xz.XZCompressorInputStream

/**
 *
 * @author Alexander Weigl
 * @version 1 (7/26/25)
 */
abstract class ExtractXz : DefaultTask() {
    @get:InputFile
    abstract val input: RegularFileProperty

    @get:OutputFile
    abstract val output: RegularFileProperty

    @TaskAction
    fun uncompress() {
        XZCompressorInputStream(input.get().asFile.inputStream()).use { input ->
            output.get().asFile.outputStream().use { output ->
                input.copyTo(output)
            }
        }
    }
}