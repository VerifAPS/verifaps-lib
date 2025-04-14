package edu.kit.iti.formal.stvs.logic.io

import edu.kit.iti.formal.stvs.logic.io.xml.XmlConfigExporter
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConstraintSpecExporter
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionExporter
import edu.kit.iti.formal.stvs.logic.io.xml.verification.GeTeTaExporter
import edu.kit.iti.formal.stvs.logic.io.xml.xml
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.code.Code
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import org.jdom2.output.Format
import org.jdom2.output.XMLOutputter
import java.io.File
import java.io.IOException
import java.io.OutputStream

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
    @Throws(ExportException::class)
    fun exportSpec(spec: ConstraintSpecification, format: ExportFormat, out: OutputStream) {
        return when (format) {
            ExportFormat.XML -> XmlConstraintSpecExporter().export(spec, out)
            ExportFormat.GETETA -> GeTeTaExporter().export(spec, out)
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
    @Throws(IOException::class, ExportException::class)
    fun exportSpec(spec: ConstraintSpecification, format: ExportFormat, file: File) {
        file.outputStream().use {
            exportSpec(spec, format, it)
        }
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
    fun exportConfig(config: GlobalConfig, out: OutputStream) {
        return XmlConfigExporter().export(config, out)
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
    @Throws(IOException::class, ExportException::class)
    fun exportConfig(config: GlobalConfig, file: File) {
        file.outputStream().use {
            exportConfig(config, it)
        }
    }

    /**
     * Exports a [StvsRootModel] using the specified [ExportFormat].
     *
     * @param session The root model that should be exported
     * @return The stream the exported object is written to
     * @throws ExportException if an error occurred while exporting
     */
    @Throws(ExportException::class)
    fun exportSession(session: StvsRootModel, out: OutputStream) {
        return XmlSessionExporter().export(session, out)
    }

    /**
     * Exports a [StvsRootModel] to a given file.
     *
     * @param session The session that should be exported
     * @param file The file to write to
     * @throws IOException if an error occurred while saving
     * @throws ExportException if an error occurred while exporting
     */
    @Throws(IOException::class, ExportException::class)
    fun exportSession(session: StvsRootModel, file: File) {
        file.outputStream().use { exportSession(session, it) }
    }

    /**
     * Exports a [Code] to the file specified in [Code.filename].
     *
     * @param code The code to export
     * @throws IOException if an error occurs while saving
     */
    @Throws(IOException::class)
    fun exportCode(code: Code) {
        exportCode(code, File(code.filename!!))
    }

    /**
     * Exports a [Code] to a given file.
     *
     * @param code The code that should be exported
     * @param file The file to write to
     * @throws IOException if an error occurs while saving
     */
    @Throws(IOException::class)
    fun exportCode(code: Code, file: File) {
        file.bufferedWriter().use {
            it.write(code.sourcecode)
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
    @Throws(ExportException::class, IOException::class)
    fun exportHistory(history: History, file: File) {
        val exportHistory = xml("history") {
            history.filenames.forEach { "filename" { +it } }
        }
        val xmlOutputter = XMLOutputter(Format.getPrettyFormat().setEncoding("utf-8"))
        file.bufferedWriter().use { xmlOutputter.output(exportHistory, it) }
    }

    enum class ExportFormat {
        XML, GETETA
    }
}
