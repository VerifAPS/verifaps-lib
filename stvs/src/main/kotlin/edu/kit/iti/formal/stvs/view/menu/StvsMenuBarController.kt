package edu.kit.iti.formal.stvs.view.menu

import edu.kit.iti.formal.stvs.logic.examples.ExamplesFacade
import edu.kit.iti.formal.stvs.logic.io.*
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.code.Code
import edu.kit.iti.formal.stvs.model.examples.Example
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import edu.kit.iti.formal.stvs.view.Controller
import edu.kit.iti.formal.stvs.view.ViewUtils
import edu.kit.iti.formal.stvs.view.common.AlertFactory.createAlert
import edu.kit.iti.formal.stvs.view.common.FileChooserFactory
import javafx.beans.property.ObjectProperty
import javafx.beans.property.SimpleObjectProperty
import javafx.collections.ListChangeListener
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.control.*
import javafx.stage.FileChooser
import java.io.*
import java.util.*

/**
 * Created by csicar on 10.01.17. Controller for the MenuBar at the top of the window does just fire
 * to the root controller
 *
 * @author Carsten Csiky
 */
class StvsMenuBarController(rootModel: ObjectProperty<StvsRootModel>) : Controller {
    // create view
    override val view: StvsMenuBar = StvsMenuBar()

    // set own properties
    private val rootModel: ObjectProperty<StvsRootModel> = rootModel
    private val lastDirectory = SimpleObjectProperty(File("."))

    /**
     * create a StvsMenuBarController; the parameters will be modified.
     *
     * @param rootModel the applications root model
     */
    init {
        rootModel.get().history.filenames.addListener(HistoryFilenamesChangeListener())
        // Fill history menu
        updateHistoryMenu()

        // add listener
        view.newCode.onAction = EventHandler { actionEvent: ActionEvent -> this.createNewCode(actionEvent) }
        view.newSpec.onAction = EventHandler { actionEvent: ActionEvent -> this.createNewSpec(actionEvent) }
        view.open.onAction = EventHandler { t: ActionEvent -> this.openFile(t) }
        view.openSession.onAction = EventHandler { t: ActionEvent -> this.openSession(t) }
        view.openCode.onAction = EventHandler { t: ActionEvent -> this.openCode(t) }
        view.openSpec.onAction = EventHandler { t: ActionEvent -> this.openSpec(t) }
        view.saveAll.onAction = EventHandler { t: ActionEvent -> this.saveAll(t) }
        view.saveSessionAs.onAction = EventHandler { actionEvent: ActionEvent -> this.saveSessionAs(actionEvent) }
        view.saveCode.onAction = EventHandler { t: ActionEvent -> this.saveCode(t) }
        view.saveSpec.onAction = EventHandler { t: ActionEvent -> this.saveSpec(t) }
        view.config.onAction = EventHandler { t: ActionEvent -> this.openConfigDialog(t) }
        view.wizard.onAction = EventHandler { actionEvent: ActionEvent -> this.openWizard(actionEvent) }
        view.about.onAction = EventHandler { actionEvent: ActionEvent -> this.openAboutDialog(actionEvent) }

        //popluate examples
        for (ex in ExamplesFacade.examples) {
            val a = ex
            val mex = MenuItem(ex.name)
            mex.onAction = EventHandler { value: ActionEvent? -> this.openExample(a) }
            mex.isMnemonicParsing = true
            Tooltip.install(mex.graphic, Tooltip(ex.description))
            view.examples.items.add(mex)
        }
    }

    fun openExample(ex: Example) {
        val url = ex.sessionFile
        try {
            val session: StvsRootModel = ImporterFacade.importSession(
                url!!.openStream(),
                rootModel.get().globalConfig,
                rootModel.get().history
            )

            //session.filename = null
            rootModel.set(session)

            if (null != ex.htmlHelp) {
                ViewUtils.openHelpText(
                    "Help for " + ex.name + " Example",
                    ex.htmlHelp
                )
            }
        } catch (e: ImportException) {
            e.printStackTrace()
        } catch (e: IOException) {
            e.printStackTrace()
        }
    }

    private fun updateHistoryMenu() {
        view.openRecentItems.clear()
        for (filename in rootModel.get().history.filenames) {
            val newItem = MenuItem(filename)
            newItem.onAction = EventHandler { _: ActionEvent? -> doOpenFile(File(filename)) }
            view.openRecentItems.add(newItem)
        }
        view.openRecent.items.clear()
        view.openRecent.items.addAll(view.openRecentItems)
    }


    private fun openWizard(actionEvent: ActionEvent) {
        WelcomeWizard(rootModel.get().globalConfig).showAndWait()
    }


    private fun doOpenFile(file: File) {
        try {
            ImporterFacade.importFile(file.toPath(), rootModel.get().globalConfig,
                rootModel.get().history, ImportHybridSpecificationHandler { hybridSpecification: HybridSpecification? ->
                    // handle hybridspecification
                    rootModel.get().hybridSpecifications
                        .add(hybridSpecification)
                }, ImportStvsRootModelHandler { rootModel ->
                    // handle rootModel
                    rootModel.workingdir = file.getParentFile()
                    rootModel.filename = file.getName()
                    this.rootModel.setValue(rootModel)
                }, (ImportCodeHandler { code: Code? ->
                    // handle code
                    rootModel.get().scenario.code = code
                })
            )
            rootModel.get().history.addFilename(file.absolutePath)
        } catch (ex: IOException) {
            createAlert(
                Alert.AlertType.ERROR, "File Open Error",
                "An error occurred while opening a file.",
                "The file " + file.absolutePath
                        + " could not be opened.", ex.message
            )
                .showAndWait()
        } catch (ex: ImportException) {
            createAlert(
                Alert.AlertType.ERROR, "File Open Error",
                "An error occurred while opening a file.",
                "The file " + file.absolutePath
                        + " could not be opened.", ex.message
            )
                .showAndWait()
        }
    }


    private fun saveSessionAs(actionEvent: ActionEvent) {
        val fileChooser = FileChooserFactory.createSaveFileChooser(
            FileChooserFactory.FileType.SESSION,
            rootModel.get().workingdir
        )
        val chosenFile: File = fileChooser
            .showSaveDialog(view.scene.window)
        if (chosenFile != null) {
            handleSaveAll(chosenFile)
            setWorkingDir(chosenFile)
        }
    }

    private fun createNewSpec(actionEvent: ActionEvent) {
        rootModel.get().addNewHybridSpec()
    }

    private fun createNewCode(actionEvent: ActionEvent) {
        var clear = false
        if (rootModel.get().scenario.code.sourcecode.isNotEmpty()) {
            val save: ButtonType = ButtonType("Save", ButtonBar.ButtonData.APPLY)
            val request = Alert(
                Alert.AlertType.CONFIRMATION, "Do you really want to throw away your code?",
                ButtonType.YES, save, ButtonType.NO
            )
            //request.initOwner();
            val answer: Optional<ButtonType> = request.showAndWait()
            if (answer.isPresent()) {
                if (answer.get() == save) {
                    clear = saveCode(actionEvent)
                }
                if (answer.get() == ButtonType.YES) {
                    clear = true
                }
            }
            if (clear) rootModel.get().scenario.code = Code()
        }
    }

    private fun openConfigDialog(t: ActionEvent) {
        val dialogManager = ConfigDialogManager(
            rootModel.get().globalConfig
        )
        dialogManager.showAndWait()
    }


    private fun openAboutDialog(actionEvent: ActionEvent) {
        val dialog: Dialog<*> = Dialog<Any?>()
        val pane = AboutDialogPane()
        dialog.title = "About"
        dialog.dialogPane = pane

        dialog.showAndWait()
    }

    private fun openCode(t: ActionEvent) {
        val fileChooser: FileChooser =
            FileChooserFactory.createOpenFileChooser(FileChooserFactory.FileType.CODE, rootModel.get().workingdir)
        val chosenFile = fileChooser.showOpenDialog(view.scene.window)
        if (chosenFile == null) {
            return
        }
        try {
            val code: Code = ImporterFacade.importStCode(chosenFile.toPath())
            rootModel.get().scenario.code = code
            rootModel.get().history
                .addFilename(chosenFile.absolutePath)
            setWorkingDir(chosenFile)
        } catch (e: IOException) {
            createAlert(e).showAndWait()
        }
    }

    private fun openSession(t: ActionEvent) {
        val fileChooser: FileChooser = FileChooserFactory.createOpenFileChooser(
            FileChooserFactory.FileType.SESSION,
            rootModel.get().workingdir
        )
        val chosenFile: File = fileChooser
            .showOpenDialog(view.scene.window)

        if (chosenFile == null) {
            return
        }
        try {
            val model: StvsRootModel = ImporterFacade.importSession(
                chosenFile.toPath(),
                rootModel.get().globalConfig,
                rootModel.get().history
            )
            setWorkingDir(chosenFile)
            model.filename = chosenFile.getName()
            rootModel.set(model)
            rootModel.get().history
                .addFilename(chosenFile.absolutePath)
        } catch (exception: IOException) {
            createAlert(exception).showAndWait()
        } catch (exception: ImportException) {
            createAlert(exception).showAndWait()
        }
    }

    private fun openSpec(t: ActionEvent) {
        val fileChooser: FileChooser = FileChooserFactory.createOpenFileChooser(
            FileChooserFactory.FileType.SPECIFICATION,
            rootModel.get().workingdir
        )
        val chosenFile = fileChooser.showOpenDialog(view.scene.window)
        if (chosenFile == null) {
            return
        }
        try {
            val spec: HybridSpecification = ImporterFacade.importHybridSpec(chosenFile.toPath())
            rootModel.get().hybridSpecifications.add(spec)
            rootModel.get().history
                .addFilename(chosenFile.absolutePath)
            setWorkingDir(chosenFile)
        } catch (e: IOException) {
            createAlert(e).showAndWait()
        } catch (e: ImportException) {
            createAlert(e).showAndWait()
        }
    }

    private fun openFile(t: ActionEvent) {
        val fileChooser: FileChooser =
            FileChooserFactory.createOpenFileChooser(FileChooserFactory.FileType.ANY, rootModel.get().workingdir)
        val chosenFile = fileChooser.showOpenDialog(view.scene.window)

        if (chosenFile == null) {
            return
        }
        doOpenFile(chosenFile)
        setWorkingDir(chosenFile)
    }

    private fun saveAll(t: ActionEvent) {
        if (rootModel.get().filename.isEmpty()) {
            val fileChooser: FileChooser = FileChooserFactory.createSaveFileChooser(
                FileChooserFactory.FileType.SESSION,
                rootModel.get().workingdir
            )
            val chosenFile = fileChooser.showSaveDialog(view.scene.window)
            if (chosenFile != null) {
                handleSaveAll(chosenFile)
            }
        } else {
            handleSaveAll(
                File(
                    rootModel.get().workingdir,
                    rootModel.get().filename
                )
            )
        }
    }

    private fun handleSaveAll(path: File) {
        try {
            rootModel.get().workingdir = path.getParentFile()
            rootModel.get().filename = path.getName()
            ExporterFacade.exportSession(
                rootModel.get(),
                path.toPath()
            )
        } catch (exception: IOException) {
            createAlert(exception).showAndWait()
        } catch (exception: ExportException) {
            createAlert(exception).showAndWait()
        }
    }

    private fun saveCode(t: ActionEvent): Boolean {
        // Set the code filename, if no filename set yet
        val code: Code = rootModel.get().scenario.code
        if (code.filename!!.isEmpty()) {
            val fileChooser: FileChooser = FileChooserFactory.createSaveFileChooser(
                FileChooserFactory.FileType.CODE,
                rootModel.get().workingdir
            )
            val chosenFile = fileChooser.showSaveDialog(view.scene.window)
            if (chosenFile == null) {
                return false
            }
            code.filename = chosenFile.absolutePath
        }
        // Export the code to the file
        try {
            ExporterFacade.exportCode(code, false)
            return true
        } catch (e: IOException) {
            createAlert(e).showAndWait()
            return false
        }
    }

    private fun saveSpec(t: ActionEvent) {
        try {
            val spec = rootModel.get().scenario.activeSpec
            if (spec == null) { // There is no active specification tab open yet
                createAlert(
                    Alert.AlertType.ERROR,
                    "Save Specification", "No specification available.", ""
                )
                    .showAndWait()
            } else {
                val fileChooser = FileChooserFactory.createSaveFileChooser(
                    FileChooserFactory.FileType.SPECIFICATION,
                    rootModel.get().workingdir
                )
                val specFile: File = fileChooser
                    .showSaveDialog(view.scene.window)
                ExporterFacade.exportSpec(
                    spec, ExporterFacade.ExportFormat.XML,
                    specFile
                )
            }
        } catch (e: ExportException) {
            createAlert(e).showAndWait()
        } catch (e: IOException) {
            createAlert(e).showAndWait()
        }
    }

    fun setWorkingDir(workingDir: File) {
        rootModel.get().workingdir = if (workingDir.isDirectory()) workingDir else workingDir.getParentFile()
    }

    private inner class HistoryFilenamesChangeListener : ListChangeListener<String?> {
        override fun onChanged(change: ListChangeListener.Change<out String>) {
            updateHistoryMenu()
        }
    }
}
