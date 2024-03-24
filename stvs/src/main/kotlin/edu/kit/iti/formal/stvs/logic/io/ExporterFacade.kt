package edu.kit.iti.formal.stvs.logic.io

import com.google.gson.GsonBuilder
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.code.*
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import java.io.*
import java.nio.file.Path
import kotlin.io.path.bufferedWriter
import kotlin.io.path.outputStream

val jsonFormat = GsonBuilder()
    .setPrettyPrinting()
    .create()

/**
 * Facade class for facilitating the export of different objects to different export formats.
 *
 * @author Benjamin Alt
 */
object ExporterFacade {

    /**
     * Exports a [ConstraintSpecification] using the specified [ExportFormat].
     *
     * @param spec The specification that should be exported
     * @param format The format for exporting
     * @return The stream the exported object is written to
     * @throws ExportException if an error occurred while exporting
     */
    @JvmStatic
    @Throws(ExportException::class)
    fun exportSpec(spec: ConstraintSpecification?, format: ExportFormat?): ByteArrayOutputStream {
        return when (format) {
            //ExportFormat.XML -> XmlConstraintSpecExporter().export(spec)
            //ExportFormat.GETETA -> GeTeTaExporter().export(spec)
            else -> throw ExportException("Unsupported export format")
        }
    }

    /**
     * Exports a [ConstraintSpecification] to a given file.
     *
     * @param spec The spec to export
     * @param format The format to use
     * @param file The file to write to
     * @throws IOException if an error occurred while saving
     * @throws ExportException if an error occurred while exporting
     */
    @JvmStatic
    @Throws(IOException::class, ExportException::class)
    fun exportSpec(spec: ConstraintSpecification?, format: ExportFormat?, file: File) {
        //writeToFile(exportSpec(spec, format), file)
    }

    /**
     * Exports a [GlobalConfig] using the specified [ExportFormat].
     *
     * @param config The configuration that should be exported
     * @param format The format for exporting
     * @return The stream the exported object is written to
     * @throws ExportException if an error occurred while exporting
     */
    @Throws(ExportException::class)
    fun exportConfig(config: GlobalConfig, writer: Writer) {
        jsonFormat.toJson(config, writer)
    }

    /**
     * Exports a [GlobalConfig] to a given file.
     *
     * @param config The config that should be exported
     * @param format The format to use
     * @param file The file to write to
     * @throws IOException if an error occurred while saving
     * @throws ExportException if an error occurred while exporting
     */
    @JvmStatic
    @Throws(IOException::class, ExportException::class)
    fun exportConfig(config: GlobalConfig, file: Path) {
        file.bufferedWriter().use { exportConfig(config, it) }
    }

    /**
     * Exports a [StvsRootModel] using the specified [ExportFormat].
     *
     * @param session The root model that should be exported
     * @return The stream the exported object is written to
     * @throws ExportException if an error occurred while exporting
     */
    @Throws(ExportException::class)
    fun exportSession(session: StvsRootModel, out: Writer) {
        jsonFormat.toJson(session, out)
    }

    /**
     * Exports a [StvsRootModel] to a given file.
     *
     * @param session The session that should be exported
     * @param file The file to write to
     * @throws IOException if an error occurred while saving
     * @throws ExportException if an error occurred while exporting
     */
    @JvmStatic
    @Throws(IOException::class, ExportException::class)
    fun exportSession(session: StvsRootModel, file: Path) {
        file.bufferedWriter().use { exportSession(session, it) }
    }

    /**
     * Exports a [Code] to the file specified in [Code.getFilename].
     *
     * @param code The code to export
     * @param escapeVariables Specifies if variables should be escaped
     * @throws IOException if an error occurs while saving
     */
    @Throws(IOException::class)
    fun exportCode(code: Code, escapeVariables: Boolean) {
        exportCode(code, File(code.filename), escapeVariables)
    }

    /**
     * Exports a [Code] to a given file.
     *
     * @param code The code that should be exported
     * @param file The file to write to
     * @param escapeVariables Specifies if variables should be escaped
     * @throws IOException if an error occurs while saving
     */
    @Throws(IOException::class)
    fun exportCode(code: Code, file: File, escapeVariables: Boolean) {
        file.bufferedWriter().use { writer ->
            if (escapeVariables) {
                writer.write(VariableEscaper.escapeCode(code))
            } else {
                writer.write(code.sourcecode)
            }
        }
    }

    /**
     * Exports a [History] to a file.
     *
     * @param history The history to export
     * @param file The file to write ro
     * @throws IOException if an error occurred while saving
     * @throws ExportException if an error occurred while exporting
     */
    fun exportHistory(history: History, file: Path) {
        file.bufferedWriter().use { out -> jsonFormat.toJson(history, out) }
    }

    /**
     * Write an OutputStream to a file.
     *
     * @param outputStream The stream to write to a file
     * @param file The file to write to
     * @throws IOException if an error occurred during file I/O
     */
    @Throws(IOException::class)
    private fun writeToFile(outputStream: ByteArrayOutputStream, file: File) {
        FileOutputStream(file).use { fostream ->
            outputStream.writeTo(fostream)
            fostream.close()
        }
    }

    enum class ExportFormat {
        XML, GETETA
    }
}
