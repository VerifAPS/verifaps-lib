package edu.kit.iti.formal.stvs.logic.io

import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.code.*
import edu.kit.iti.formal.stvs.model.common.*
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.ValueBool
import edu.kit.iti.formal.stvs.model.table.*
import edu.kit.iti.formal.stvs.model.verification.VerificationResult
import edu.kit.iti.formal.stvs.model.verification.VerificationSuccess
import javafx.beans.property.*
import kotlinx.serialization.Serializable
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.decodeFromStream
import kotlinx.serialization.json.encodeToStream
import org.apache.commons.io.IOUtils
import org.xml.sax.InputSource
import org.xml.sax.SAXException
import tornadofx.asObservable
import java.io.*
import java.nio.file.Path
import javax.xml.parsers.DocumentBuilderFactory
import javax.xml.parsers.ParserConfigurationException
import kotlin.io.path.inputStream
import kotlin.io.path.outputStream
import kotlin.io.path.readText


val jsonFormat = Json {
    prettyPrint = true
    ignoreUnknownKeys = true
}

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
     * @return The stream the exported object is written to
     * @throws ExportException if an error occurred while exporting
     */
    @JvmStatic
    @Throws(ExportException::class)
    fun exportSpec(spec: ConstraintSpecification, out: OutputStream) {

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
    fun exportSpec(spec: ConstraintSpecification, file: File) = file.outputStream().use { exportSpec(spec, it) }

    /**
     * Exports a [GlobalConfig] using the specified [ExportFormat].
     *
     * @param config The configuration that should be exported
     * @param format The format for exporting
     * @return The stream the exported object is written to
     * @throws ExportException if an error occurred while exporting
     */
    @Throws(ExportException::class)
    fun exportConfig(config: GlobalConfig, ou: OutputStream) {
        jsonFormat.encodeToStream(config.serialize(), ou)
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
        file.outputStream().use { exportConfig(config, it) }
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
        val s = session.serialize()
        jsonFormat.encodeToStream(s, out)
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
        file.outputStream().use { exportSession(session, it) }
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
        file.bufferedWriter().use {
            if (escapeVariables) {
                it.write(VariableEscaper.escapeCode(code))
            } else {
                it.write(code.sourcecode)
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
        file.outputStream().use { out -> jsonFormat.encodeToStream(history, out) }
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

/**
 * Facade class for facilitating the import of different objects from different formats.
 *
 * @author Benjamin Alt
 */
object ImporterFacade {
    /**
     * Imports a [ConstraintSpecification] from an [InputStream] using the specified
     * [ImportFormat].
     *
     * @param input The stream from which the specification should be imported
     * @return The imported specification
     * @throws ImportException if an error occurred during importing
     */
    @JvmStatic
    @Throws(ImportException::class)
    fun importConstraintSpec(input: InputStream): ConstraintSpecification {
        val data = fromJson<SpecificationTableData>(input)
        return data.asConstraintSpecification()
    }

    /**
     * Imports a [ConstraintSpecification] from a file.
     *
     * @param file The file to import from
     * @return The imported specification
     * @throws IOException if an error occurred while reading the file
     * @throws ImportException if an error occurred while importing
     */
    @Throws(IOException::class, ImportException::class)
    fun importConstraintSpec(file: Path): ConstraintSpecification {
        return importConstraintSpec(file.inputStream())
    }

    /**
     * Imports a [ConcreteSpecification] from an [InputStream] using the specified
     * [ImportFormat].
     *
     * @param input The stream from which to import from
     * @param typeContext A list of types used in the specification
     * @return The imported specification
     * @throws ImportException if an error occurred during importing
     */
    @Throws(ImportException::class)
    fun importConcreteSpec(input: InputStream, typeContext: List<Type>): ConcreteSpecification {
        val data = fromJson<SpecificationTableData>(input)

        require(data.isConcrete)

        val seq = data.freeVariables.map { it.deserialize() }.toMutableList()
        val free = FreeVariableList(seq)
        val s = ConcreteSpecification(data.isCounterExample)
        s.name = data.name

        // Add the columnHeaders (column headers)
        for (v in data.variables) {
            s.columnHeaders.add(ValidIoVariable(v.category, v.name,
                typeContext.find { it.typeName == v.type } ?: error("Could not find type ${v.type}")))
        }
        val columnNames = data.variables.map { it.name }

        data.rows.forEachIndexed { _, it ->
            val newDuration = ConcreteDuration(0, it.duration.toInt())
            s.durations.add(newDuration)

            if (it.cells.size != columnNames.size) {
                throw ImportException("Row too short: Do not have a cell for each IOVariable")
            }

            val cellsMap =
                columnNames.zip(it.cells).associate { (col, _) ->
                    val constraintCell = ConcreteCell(ValueBool.TRUE)//TODO weigl
                    col to constraintCell
                }
            val newRow = SpecificationRow.createUnobservableRow(cellsMap)
            s.rows.add(newRow)
        }
        return s
    }

    /**
     * Imports a [ConcreteSpecification] from a file.
     *
     * @param file The file to import from
     * @param typeContext A list of types used in the specification
     * @return The imported specification
     * @throws IOException if an error occurred while reading the file
     * @throws ImportException if an error occurred while importing
     */
    @Throws(IOException::class, ImportException::class)
    fun importConcreteSpec(file: Path, typeContext: List<Type>): ConcreteSpecification {
        return importConcreteSpec(file.inputStream(), typeContext)
    }

    /**
     * Imports a [HybridSpecification] from an [InputStream] using the specified
     * [ImportFormat].
     *
     * @param input The stream from which to import from
     * @return The imported specification
     * @throws ImportException if an error occurred during importing
     */
    @JvmStatic
    @Throws(ImportException::class)
    fun importHybridSpec(input: InputStream): HybridSpecification {
        //        ImportFormat.XML -> {
        //val constraintSpec: ConstraintSpecification = XmlConstraintSpecImporter().doImport(input)
        //return HybridSpecification(constraintSpec, true)
        //      }
        return fromJson<HybridSpecification>(input)
    }

    /**
     * Imports a [HybridSpecification] from a file.
     *
     * @param file The file to import from.
     * @return The imported specification
     * @throws IOException if an error occured while reading file.
     * @throws ImportException if an error occured while importing.
     */
    @Throws(IOException::class, ImportException::class)
    fun importHybridSpec(file: Path): HybridSpecification {
        return importHybridSpec(file.inputStream())
    }

    /**
     * Imports a [GlobalConfig] from an [InputStream] using the specified
     * [ImportFormat].
     *
     * @param input The stream from which to import from
     * @return The imported config
     * @throws ImportException exception during importing
     */
    @JvmStatic
    @Throws(ImportException::class)
    fun importConfig(input: InputStream): GlobalConfig {
        return fromJson<GlobalConfigData>(input).deserialize()
    }

    private inline fun <reified T> fromJson(input: InputStream): T {
        return jsonFormat.decodeFromStream<T>(input)!!
    }

    /**
     * Imports a [GlobalConfig] from a file.
     *
     * @param file The file to import from.
     * @return The imported config
     * @throws FileNotFoundException Exception if file not found.
     * @throws ImportException if an error occured while importing.
     */
    @Throws(FileNotFoundException::class, ImportException::class)
    fun importConfig(file: Path): GlobalConfig {
        file.inputStream().use { return importConfig(it) }
    }

    /**
     * Imports a [VerificationResult] from an [InputStream] using the specified
     * [ImportFormat].
     *
     * @param input The stream from which to import from
     * @param typeContext Types in the verified specification
     * @param constraintSpec The constraint specification for which to import a verification result
     * @return The imported result
     * @throws ImportException exception during importing
     */
    @Throws(ImportException::class)
    fun importVerificationResult(
        input: InputStream,
        typeContext: List<Type>,
        constraintSpec: ConstraintSpecification
    ): VerificationResult {
        return VerificationSuccess(File("."))
    }

    /**
     * Imports a [StvsRootModel] from an [InputStream] using the specified
     * [ImportFormat].
     *
     * @param input The stream from which to import from
     * @param currentConfig config to be used for the model
     * @param currentHistory history to be used for the model
     * @return The imported model
     * @throws ImportException exception during importing
     */
    @Throws(ImportException::class)
    fun importSession(input: InputStream, currentConfig: GlobalConfig, currentHistory: History): StvsRootModel {
        val session = fromJson<Session>(input)
        return StvsRootModel(
            session.tabs.map {
                val s = it.specification.first().asConstraintSpecification()
                HybridSpecification(s, true)
            }.asObservable(),
            currentConfig,
            currentHistory
        )
    }

    /**
     * Imports a [StvsRootModel] from a file.
     *
     * @param file The file to import from.
     * @param currentConfig config to be used for the model
     * @param currentHistory history to be used for the model
     * @return The imported model
     * @throws IOException if an error occured while reading the file
     * @throws ImportException if an error occured while importing
     */
    @Throws(IOException::class, ImportException::class)
    fun importSession(file: Path, currentConfig: GlobalConfig, currentHistory: History): StvsRootModel {
        file.inputStream().use {
            return importSession(it, currentConfig, currentHistory)
        }
    }

    /**
     * Imports a [Code] from a file.
     *
     * @param chosenFile file to import from.
     * @return The imported code
     * @throws IOException if an error occured while reading the file
     */
    @Throws(IOException::class)
    fun importStCode(chosenFile: Path): Code {
        val plaintext = chosenFile.readText()
        return Code(chosenFile.toString(), plaintext)
    }

    /**
     * Imports a [History] from a file.
     *
     * @param chosenFile The file to import from
     * @return The imported history
     * @throws ImportException if an error occured while importing
     */
    fun importHistory(chosenFile: Path): History {
        try {
            chosenFile.inputStream().use {
                return fromJson<History>(it)
            }
        } catch (e: IOException) {
            throw ImportException(e.message, e)
        }
    }

    /**
     * Imports a file of unknown type.
     *
     * @param file The file to open
     * @param globalConfig The current global config
     * @param currentHistory history of the opened files to this point
     * @param importHybridSpecificationHandler A file handler (invoked if the file is a Specification)
     * @param importStvsRootModelHandler A file handler (invoked if the file is a Session)
     * @param codeConsumer A file handler (invoked if the file is a code file)
     * @throws IOException general io exception
     * @throws ImportException general importing exception
     */
    @Throws(IOException::class, ImportException::class)
    fun importFile(
        file: Path,
        globalConfig: GlobalConfig,
        currentHistory: History,
        importHybridSpecificationHandler: ImportHybridSpecificationHandler,
        importStvsRootModelHandler: ImportStvsRootModelHandler,
        codeConsumer: ImportCodeHandler
    ) {
        val writer = StringWriter()
        val byteArray: ByteArray = IOUtils.toByteArray(file.inputStream())
        IOUtils.copy(ByteArrayInputStream(byteArray), writer, "utf8")
        val inputString = writer.toString()
        val dbf = DocumentBuilderFactory.newInstance()
        dbf.isNamespaceAware = true
        try {
            val doc = dbf.newDocumentBuilder().parse(InputSource(StringBufferInputStream(inputString)))
            if (doc != null && doc.firstChild != null) {
                val rootNode = doc.firstChild
                when (rootNode.nodeName) {
                    "session" -> {
                        importStvsRootModelHandler.accept(importSession(file, globalConfig, currentHistory))
                        return
                    }

                    "specification" -> {
                        importHybridSpecificationHandler.accept(importHybridSpec(file))
                        return
                    }

                    else -> {
                        codeConsumer.accept(importStCode(file))
                        return
                    }
                }
            }
        } catch (e: SAXException) {
            // ignore, because it might have been code
        } catch (_: ParserConfigurationException) {
        } catch (_: ImportException) {
        }
        codeConsumer.accept(importStCode(file))
    }

    enum class ImportFormat
}

private fun SpecificationTableData.asConstraintSpecification(): ConstraintSpecification {
    val free = FreeVariableList(freeVariables.map { it.deserialize() }.toMutableList())
    val s = ConstraintSpecification(name, free)
    s.comment = comment


    // Add the columnHeaders (column headers)
    for (v in variables) {
        s.columnHeaders.add(SpecIoVariable(v.category, v.role, v.type, v.name)
            .also { it.comment = v.comment })
    }
    val columnNames = variables.map { it.name }

    rows.forEachIndexed { _, it ->
        val newDuration = ConstraintDuration(it.duration)
        //newDuration.comment = it.duration.comment
        s.durations.add(newDuration)

        if (it.cells.size != columnNames.size) {
            throw ImportException("Row too short: Do not have a cell for each IOVariable")
        }

        val cellsMap =
            columnNames.zip(it.cells).associate { (col, cell) ->
                val constraintCell = ConstraintCell(cell)
                //constraintCell.comment = cell.comment
                col to constraintCell
            }
        val newRow = ConstraintSpecification.createRow(cellsMap)
        newRow.comment = it.comment
        s.rows.add(newRow)
    }
    return s
}

private fun FreeVar.deserialize() = FreeVariable(name, type, constraint)

private fun StvsRootModel.serialize(): Session {
    val tabs = this.serializeTabs()
    val code = scenario.code.serialize()
    return Session(
        code = code, tabs = tabs//, config = globalConfig.serialize(), history = history.filenames.toList()
    )
}

@Serializable
data class CodeData(val fileName: String?, val content: String)

private fun Code.serialize() = CodeData(filename, sourcecode)
private fun CodeData.deserialize() = Code(fileName, content)

@Serializable
data class GlobalConfigData(
    var verificationTimeout: Int,
    var simulationTimeout: Int,
    var windowMaximized: Boolean,
    var windowHeight: Int,
    var windowWidth: Int,
    var uiLanguage: String,
    var maxLineRollout: Int,
    var editorFontSize: Int,
    var editorFontFamily: String,
    var showLineNumbers: Boolean,
    var nuxmvFilename: String,
    var z3Path: String,
    var getetaCommand: String
)

private fun GlobalConfig.serialize() = GlobalConfigData(
    verificationTimeout = verificationTimeout,
    simulationTimeout = simulationTimeout,
    windowMaximized = windowMaximized,
    windowHeight = windowHeight,
    windowWidth = windowWidth,
    uiLanguage = uiLanguage,
    maxLineRollout = maxLineRollout,
    editorFontSize = editorFontSize,
    editorFontFamily = editorFontFamily,
    showLineNumbers = showLineNumbers,
    nuxmvFilename = nuxmvFilename,
    z3Path = z3Path,
    getetaCommand = getetaCommand
)

private fun GlobalConfigData.deserialize(): GlobalConfig = GlobalConfig().also {
    it.verificationTimeout = verificationTimeout
    it.simulationTimeout = simulationTimeout
    it.windowMaximized = windowMaximized
    it.windowHeight = windowHeight
    it.windowWidth = windowWidth
    it.uiLanguage = uiLanguage
    it.maxLineRollout = maxLineRollout
    it.editorFontSize = editorFontSize
    it.editorFontFamily = it.editorFontFamily
    it.showLineNumbers = showLineNumbers
    it.nuxmvFilename = nuxmvFilename
    it.z3Path = z3Path
    it.getetaCommand = getetaCommand
}

@Throws(ExportException::class)
private fun StvsRootModel.serializeTabs(): List<TabData> {
    return hybridSpecifications.mapIndexed { i, spec ->
        val specifications = arrayListOf<SpecificationTableData>()

        specifications.add(spec.serialize())

        val concreteSpecification = spec.getConcreteInstance() ?: spec.getCounterExample()
        if (concreteSpecification != null) specifications.add(concreteSpecification.serialize())

        TabData(
            id = i.toUInt(), open = false, readOnly = !spec.isEditable, specifications
        )
    }
}

//region conversion
private fun HybridSpecification.serialize(): SpecificationTableData {
    val variables = columnHeaders.map {
        it.serialize()
    }
    val freeVars = freeVariableList.variables.map { it.serialize() }

    return SpecificationTableData(
        name = this.name,
        variables = variables,
        freeVariables = freeVars,
        rows = makeRows(this),
        isConcrete = false,
        isCounterExample = false,
        comment = this.comment
    )
}

private fun FreeVariable.serialize() = FreeVar(name, type, constraint)
private fun SpecIoVariable.serialize() = IOVar(name, type, category, role, comment)
private fun ValidIoVariable.serialize() = IOVar(name, type, category, category.defaultRole)

private fun makeRows(constraintSpec: ConstraintSpecification) = constraintSpec.rows.mapIndexed { i, row ->
    val duration = constraintSpec.durations[i]
    val cells = constraintSpec.columnHeaders.map {
        val cell = row.cells[it.name]!!
        cell.asString?:""
        //CommentableString(cell.asString ?: "", cell.comment)
    }
    RowData(
        comment = row.comment,
        duration = duration.asString ?: "" /* CommentableString(duration.asString ?: "", duration.comment)*/,
        cells = cells
    )
}

private fun ConcreteSpecification.makeRows() = rows.mapIndexed { i, row ->
    val duration = durations[i]
    val cells = columnHeaders.map {
        val cell = row.cells[it.name]!!
        //CommentableString(cell.asString ?: "")
        cell.asString ?: ""
    }
    RowData(
        comment = row.comment,
        duration = duration.duration.toString()/* CommentableString(duration.duration.toString())*/,
        cells = cells
    )
}

private fun ConcreteSpecification.serialize(): SpecificationTableData {
    val variables = columnHeaders.map { it.serialize() }
    return SpecificationTableData(
        name = this.name,
        variables = variables,
        rows = makeRows(),
        isConcrete = false,
        isCounterExample = false,
        comment = ""
    )
}


@Serializable
data class Session(
    val code: CodeData, val tabs: List<TabData> //, val config: GlobalConfigData, val history: List<String>
)

@Serializable
data class TabData(
    val id: UInt,
    val open: Boolean = true,
    val readOnly: Boolean = false,
    val specification: List<SpecificationTableData>,
)

@Serializable
data class IOVar(
    val name: String,
    val type: String,
    val category: VariableCategory,
    val role: VariableRole,
    val comment: String? = null
)

@Serializable
data class FreeVar(val name: String, val type: String, val constraint: String)

@Serializable
data class SpecificationTableData(
    val variables: List<IOVar> = listOf(),
    val freeVariables: List<FreeVar> = listOf(),
    val rows: List<RowData> = listOf(),
    val enumTypes: Map<String, List<String>> = mapOf(),
    val isConcrete: Boolean = false,
    val isCounterExample: Boolean = false,
    val comment: String? = null,
    val name: String = "Unnamed Specification"
)

//@Serializable
//data class CommentableString(var value: String, val comment: String? = null)

@Serializable
data class RowData(
    val duration: String, val comment: String? = null, val cells: List<String>
)

//endregion