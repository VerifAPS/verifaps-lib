package edu.kit.iti.formal.stvs.logic.io

import edu.kit.iti.formal.stvs.logic.io.xml.*
import edu.kit.iti.formal.stvs.logic.io.xml.verification.GeTeTaImporter
import edu.kit.iti.formal.stvs.model.*
import edu.kit.iti.formal.stvs.model.code.*
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.table.*
import edu.kit.iti.formal.stvs.model.verification.VerificationResult
import org.xml.sax.InputSource
import org.xml.sax.SAXException
import java.io.*
import java.nio.file.Files
import java.nio.file.Paths
import javax.xml.parsers.DocumentBuilderFactory
import javax.xml.parsers.ParserConfigurationException

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
    @Throws(ImportException::class)
    fun importConstraintSpec(input: InputStream): ConstraintSpecification {
        return XmlConstraintSpecImporter().doImport(input)
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
    fun importConstraintSpec(file: File): ConstraintSpecification {
        file.inputStream().use {
            return importConstraintSpec(it)
        }
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
        return XmlConcreteSpecImporter(typeContext).doImport(input)
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
    fun importConcreteSpec(file: File, typeContext: List<Type>): ConcreteSpecification {
        file.inputStream().use {
            return importConcreteSpec(it, typeContext)
        }
    }

    /**
     * Imports a [HybridSpecification] from an [InputStream] using the specified
     * [ImportFormat].
     *
     * @param input The stream from which to import from
     * @return The imported specification
     * @throws ImportException if an error occurred during importing
     */
    @Throws(ImportException::class)
    fun importHybridSpec(input: InputStream): HybridSpecification {
        val constraintSpec = XmlConstraintSpecImporter().doImport(input)
        return HybridSpecification(constraintSpec, true)
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
    fun importHybridSpec(file: File): HybridSpecification {
        file.inputStream().use {
            return importHybridSpec(it)
        }
    }

    /**
     * Imports a [GlobalConfig] from an [InputStream] using the specified
     * [ImportFormat].
     *
     * @param input The stream from which to import from
     * @return The imported config
     * @throws ImportException exception during importing
     */
    @Throws(ImportException::class)
    fun importConfig(input: InputStream): GlobalConfig {
        return XmlConfigImporter().doImport(input)
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
    fun importConfig(file: File): GlobalConfig =
        file.inputStream().use {
            importConfig(it)
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
        input: InputStream, typeContext: List<Type>,
        constraintSpec: ConstraintSpecification
    ): VerificationResult {
        return GeTeTaImporter(typeContext, constraintSpec).doImport(input)
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
        input: InputStream, currentConfig: GlobalConfig,
        currentHistory: History
    ): StvsRootModel {
        return XmlSessionImporter(currentConfig, currentHistory).doImport(input)
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
        file: File, currentConfig: GlobalConfig,
        currentHistory: History
    ): StvsRootModel {
        return importSession(FileInputStream(file), currentConfig, currentHistory)
    }

    /**
     * Imports a [Code] from a file.
     *
     * @param chosenFile file to import from.
     * @return The imported code
     * @throws IOException if an error occured while reading the file
     */
    @Throws(IOException::class)
    fun importStCode(chosenFile: File): Code {
        val plaintext = String(
            Files.readAllBytes(Paths.get(chosenFile.getAbsolutePath())),
            charset("utf-8")
        )
        return Code(chosenFile.getAbsolutePath(), plaintext)
    }

    /**
     * Imports a [History] from a file.
     *
     * @param chosenFile The file to import from
     * @param format The format to use for importing
     * @return The imported history
     * @throws ImportException if an error occured while importing
     */
    @Throws(ImportException::class)
    fun importHistory(chosenFile: File): History {
        try {
            val root = chosenFile.inputStream().use { XmlImporter.readXml(it).rootElement }
            val filenames = root.getChildren("filename").map { it.text }
            return History(filenames)
        } catch (e: IOException) {
            throw ImportException(e)
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
        file: File, globalConfig: GlobalConfig, currentHistory: History,
        importHybridSpecificationHandler: ImportHybridSpecificationHandler,
        importStvsRootModelHandler: ImportStvsRootModelHandler,
        codeConsumer: ImportCodeHandler
    ) {
        val inputString = file.bufferedReader().readText()
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
        XML, GETETA
    }
}
