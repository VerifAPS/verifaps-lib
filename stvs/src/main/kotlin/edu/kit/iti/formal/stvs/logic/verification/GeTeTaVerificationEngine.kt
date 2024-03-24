package edu.kit.iti.formal.stvs.logic.verification

import edu.kit.iti.formal.stvs.logic.io.*
import edu.kit.iti.formal.stvs.model.common.NullableProperty
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.verification.VerificationError
import edu.kit.iti.formal.stvs.model.verification.VerificationResult
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario
import edu.kit.iti.formal.stvs.util.ProcessCreationException
import javafx.application.Platform
import javafx.beans.Observable
import org.apache.commons.io.IOUtils
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import java.io.*
import java.io.FileNotFoundException
import java.nio.charset.StandardCharsets

/**
 * Handles communication with the GeTeTa verification engine.
 *
 * @author Benjamin Alt
 */
class GeTeTaVerificationEngine(config: GlobalConfig, typeContext: List<Type>) : VerificationEngine {
    private var getetaProcess: Process?

    override val verificationResultProperty: NullableProperty<VerificationResult?> = NullableProperty()
    override val verificationResult: VerificationResult?
        get() = verificationResultProperty.get()

    private val typeContext: List<Type>
    private val config: GlobalConfig
    private var getetaOutputFile: File? = null
    private var processMonitor: ProcessMonitor? = null
    override var verificationSpecification: ConstraintSpecification? = null

    /**
     * Creates an instance based on given [GlobalConfig] and `typeContext`. The
     * `typeContext` is used later for importing the possible counterexample.
     *
     * @param config config that should be used
     * @param typeContext list of types used for importing counterexample
     * @throws FileNotFoundException nuXmv not found
     */
    init {
        getetaProcess = null
        this.typeContext = typeContext
        this.config = config

        /* Check if nuXmv executable exists */
        val nuxmvFile = File(config.nuxmvFilename)
        //TODO check if nuXmv is executable by running it.
    }

    /**
     * Exports the given [VerificationScenario] to temporary files and starts the GeTeTa
     * verification engine process.
     *
     * @param scenario scenario that hold the code to be checked
     * @param spec specification that should be checked
     * @throws IOException exception while creating process
     * @throws ExportException exception while exporting
     */
    @Throws(IOException::class, ExportException::class, ProcessCreationException::class)
    override fun startVerification(scenario: VerificationScenario, spec: ConstraintSpecification) {
        /*
     * This will create a deep copy, so that modifying the original ConstraintSpecification between
     * calling tartVerification() and getVerificationSpecification() will have no effect on the
     * possibly newly opened counter example tab.
     */

        verificationSpecification = ConstraintSpecification(spec!!)
        // Write ConstraintSpecification and Code to temporary input files for GeTeTa
        val tempSpecFile = File.createTempFile("verification-spec", ".xml")
        val tempCodeFile = File.createTempFile("verification-code", ".st")

        /*val process = createNuXMVProcess(
            folder, modules, nuXmv, VerificationTechnique.IC3
        )
        val output = process.call()
        */

        // Start verification engine in new child process
        if (getetaProcess != null) {
            cancelVerification()
        }

        val processBuilder: ProcessBuilder = ProcessBuilder("")//getetaCommand.split(" "))
        //System.out.println(getetaCommand)
        processBuilder.environment()["NUXMV"] = config.nuxmvFilename
        getetaOutputFile = File.createTempFile("verification-result", ".log")
        LOGGER.info("Code file: {}", tempCodeFile)
        LOGGER.info("Specification file: {}", tempSpecFile)
        //LOGGER.info("Verification log file: {}", getetaOutputFile.getAbsoluteFile())
        processBuilder.redirectOutput(getetaOutputFile)
        try {
            getetaProcess = processBuilder.start()
            // Find out when process finishes to set verification result property
            processMonitor = ProcessMonitor(getetaProcess, config.verificationTimeout)
            processMonitor!!.processFinishedProperty()!!.addListener { observable: Observable? -> onVerificationDone() }
            // Starts the verification process in another thread
            processMonitor!!.start()
        } catch (exception: IllegalArgumentException) {
            exception.printStackTrace()
            throw ProcessCreationException("The verification could not be launched")
        } catch (exception: ArrayIndexOutOfBoundsException) {
            exception.printStackTrace()
            throw ProcessCreationException("The verification could not be launched")
        }
    }

    override fun cancelVerification() {
        if (getetaProcess != null) {
            getetaProcess!!.destroy()
            getetaProcess = null
        }
    }

    /**
     * Handles the output of the GeTeTa verification engine.
     */
    private fun onVerificationDone() {
        if (getetaProcess == null) { // Verification was cancelled
            return
        }
        var result: VerificationResult?
        var logFile: File? = null
        val processError = processMonitor!!.error
        if (processError != null) {
            result = VerificationError(processError)
        } else {
            try {
                val processOutput = IOUtils.toString(FileInputStream(getetaOutputFile), "utf-8")
                logFile = writeLogFile(processOutput)
                val cleanedProcessOutput = cleanProcessOutput(processOutput)
                // Set the verification result depending on the GeTeTa output
                result = if (processMonitor!!.isAborted) {
                    VerificationError(VerificationError.Reason.TIMEOUT, logFile)
                } else {
                    ImporterFacade.importVerificationResult(
                        ByteArrayInputStream(cleanedProcessOutput.toByteArray(charset("utf-8"))),
                        typeContext!!, verificationSpecification!!
                    )
                }
            } catch (exception: IOException) {
                result = VerificationError(exception, logFile)
            } catch (exception: ImportException) {
                result = VerificationError(exception, logFile)
            }
        }
        // Set the verification result back in the javafx thread:
        val finalResult = result // have to do this because of lambda restrictions...
        try {
            Platform.runLater { verificationResultProperty.set(finalResult) }
        } catch (exception: IllegalStateException) {
            verificationResultProperty.set(finalResult)
        }
    }

    @Throws(IOException::class)
    private fun writeLogFile(processOutput: String): File {
        val logFile = File.createTempFile("log-verification-", ".xml")
        getetaOutputFile!!.deleteOnExit()
        val writer = PrintWriter(
            OutputStreamWriter(FileOutputStream(logFile), StandardCharsets.UTF_8), true
        )
        writer.println(processOutput)
        writer.close()
        return logFile
    }

    private fun cleanProcessOutput(processOutput: String): String {
        val xmlStartIndex = processOutput.indexOf("<")
        if (xmlStartIndex >= 0) {
            return processOutput.substring(xmlStartIndex)
        }
        return processOutput
    }

    companion object {
        private val LOGGER: Logger = LoggerFactory.getLogger(GeTeTaVerificationEngine::class.java)
    }
}
