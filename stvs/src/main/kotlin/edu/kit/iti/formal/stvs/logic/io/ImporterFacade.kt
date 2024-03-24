package edu.kit.iti.formal.stvs.logic.io

import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.code.Code
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import edu.kit.iti.formal.stvs.model.verification.VerificationResult
import edu.kit.iti.formal.stvs.model.verification.VerificationSuccess
import edu.kit.iti.formal.util.inputStream
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.json.decodeFromStream
import org.apache.commons.io.IOUtils
import org.xml.sax.InputSource
import org.xml.sax.SAXException
import java.io.*
import java.nio.file.*
import javax.xml.parsers.DocumentBuilderFactory
import javax.xml.parsers.ParserConfigurationException
import kotlin.io.path.readText

/**
 * Facade class for facilitating the import of different objects from different formats.
 *
 * @author Benjamin Alt
 */
@OptIn(ExperimentalSerializationApi::class)
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
        return ExporterFacade.jsonFormat.decodeFromStream<ConstraintSpecification>(input)
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
        //ImportFormat.XML -> return XmlConcreteSpecImporter(typeContext).doImport(input)
        TODO()
    }

    /**
     * Imports a [ConcreteSpecification] from a file.
     *
     * @param file The file to import from
     * @param format The format to use for importing
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
     * @param format The format to use for importing
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
        return ExporterFacade.jsonFormat.decodeFromStream<HybridSpecification>(input)
    }

    /**
     * Imports a [HybridSpecification] from a file.
     *
     * @param file The file to import from.
     * @param format The format to use for importing
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
     * @param format The format to use for importing
     * @return The imported config
     * @throws ImportException exception during importing
     */
    @JvmStatic
    @Throws(ImportException::class)
    fun importConfig(input: InputStream): GlobalConfig {
        return ExporterFacade.jsonFormat.decodeFromStream<GlobalConfig>(input)
    }

    /**
     * Imports a [GlobalConfig] from a file.
     *
     * @param file The file to import from.
     * @param format The format to use for importing
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
     * @param format The format to use for importing
     * @param typeContext Types in the verified specification
     * @param constraintSpec The constraint specification for which to import a verification result
     * @return The imported result
     * @throws ImportException exception during importing
     */
    @Throws(ImportException::class)
    fun importVerificationResult(
        input: InputStream, typeContext: List<Type>, constraintSpec: ConstraintSpecification
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
    fun importSession(
        input: InputStream,
        currentConfig: GlobalConfig, currentHistory: History
    ): StvsRootModel {
        return ExporterFacade.jsonFormat.decodeFromStream<StvsRootModel>(input)
        //ImportFormat.XML -> return XmlSessionImporter(currentConfig, currentHistory).doImport(input)
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
    fun importSession(
        file: Path, currentConfig: GlobalConfig, currentHistory: History
    ): StvsRootModel {
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
                return ExporterFacade.jsonFormat.decodeFromStream<History>(it)
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
        file: Path, globalConfig: GlobalConfig, currentHistory: History,
        importHybridSpecificationHandler: ImportHybridSpecificationHandler,
        importStvsRootModelHandler: ImportStvsRootModelHandler, codeConsumer: ImportCodeHandler
    ) {
        val writer = StringWriter()
        val byteArray: ByteArray = IOUtils.toByteArray(file.inputStream())
        IOUtils.copy(ByteArrayInputStream(byteArray), writer, "utf8")
        val inputString = writer.toString()
        val dbf = DocumentBuilderFactory.newInstance()
        dbf.isNamespaceAware = true
        try {
            val doc = dbf.newDocumentBuilder().parse(InputSource(StringReader(inputString)))
            if (doc != null && doc.firstChild != null) {
                val rootNode = doc.firstChild
                when (rootNode.nodeName) {
                    "session" -> {
                        importStvsRootModelHandler
                            .accept(importSession(file, globalConfig, currentHistory))
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

    enum class ImportFormat {
    }
}
