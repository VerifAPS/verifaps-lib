package edu.kit.iti.formal.stvs.model

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario
import javafx.collections.FXCollections
import javafx.collections.ObservableList
import java.io.File
import java.io.IOException
import java.util.function.Consumer
import kotlin.io.path.createDirectories
import kotlin.io.path.div
import kotlin.io.path.exists
import kotlin.io.path.isDirectory

/**
 * The model equivalent of a "session". Contains a list of [HybridSpecification]s, a
 * [GlobalConfig], a [History] and a [VerificationScenario] which has a reference
 * to the currently loaded code.
 *
 * @author Benjamin Alt
 */
class StvsRootModel @JvmOverloads constructor(
    val hybridSpecifications: ObservableList<HybridSpecification> = FXCollections.observableArrayList(),
    var globalConfig: GlobalConfig = GlobalConfig(),
    val history: History = History(),
    var scenario: VerificationScenario = VerificationScenario(),
    var workingdir: File = File(System.getProperty("user.home")),
    var filename: String = ""
) {

    /**
     * Create a new StvsRootModel from the given [HybridSpecification]s, [GlobalConfig],
     * [History], [VerificationScenario], working directory and current filename.
     *
     * @param hybridSpecifications The list of [HybridSpecification]s.
     * @param globalConfig The global configuration
     * @param history The current history
     * @param scenario The verification scenario (containing a reference to the current code)
     * @param workingdir working-directory that should be used (e.g. for opening and saving)
     * @param filename The filename of the session file. This can be used e.g. for a "Save Session"
     * file dialog or other applications when it may be useful to know where a session was
     * loaded from, or where it ought to be stored
     */
    val isFirstStart: Boolean
        get() = (GlobalConfig.CONFIG_DIRPATH / GlobalConfig.AUTOLOAD_CONFIG_FILENAME).exists().not()

    /**
     * Saves the current session to [StvsRootModel.AUTOLOAD_SESSION_FILENAME] in the directory
     * [GlobalConfig.CONFIG_DIRPATH].
     *
     * @throws IOException when the directory does not exist and cannot be created
     * @throws ExportException when there is an error during export
     */
    @Throws(IOException::class, ExportException::class)
    fun autosaveSession() {
        val configDir = GlobalConfig.CONFIG_DIRPATH
        if (!configDir.isDirectory() || !configDir.exists()) {
            configDir.createDirectories()
        }
        val sessionFile = GlobalConfig.CONFIG_DIRPATH / AUTOLOAD_SESSION_FILENAME
        ExporterFacade.exportSession(this, sessionFile.toFile())
    }

    /**
     * Adds a new [HybridSpecification] to the list accessible via
     * [StvsRootModel.getHybridSpecifications]. The new specification already includes columns
     * for variables declared in the code.
     */
    fun addNewHybridSpec() {
        val hybridSpec = HybridSpecification(FreeVariableList(), true)
        val parsedCode = scenario.code.parsedCode
        if (parsedCode != null) {
            println(parsedCode.definedTypes)
            parsedCode.definedVariables.forEach(Consumer { codeIoVariable: CodeIoVariable ->
                hybridSpec.columnHeaders.add(
                    SpecIoVariable(
                        category = codeIoVariable.category,
                        typeIdentifier = codeIoVariable.type, name = codeIoVariable.name
                    )
                )
            })
        }
        hybridSpecifications.add(hybridSpec)
    }

    companion object {
        private const val AUTOLOAD_SESSION_FILENAME = "stvs-session.xml"
        val sessionFile = GlobalConfig.CONFIG_DIRPATH / AUTOLOAD_SESSION_FILENAME

        /**
         * Loads the last session saved via [StvsRootModel.autosaveSession] (see
         * [GlobalConfig.CONFIG_DIRPATH] and [StvsRootModel.AUTOLOAD_SESSION_FILENAME].
         *
         * @return The autoloaded root model.
         */
        @JvmStatic
        fun autoloadSession(): StvsRootModel {
            return try {
                ImporterFacade.importSession(sessionFile.toFile(), GlobalConfig(), History())
            } catch (e: Exception) {
                StvsRootModel()
            }
        }
    }
}
