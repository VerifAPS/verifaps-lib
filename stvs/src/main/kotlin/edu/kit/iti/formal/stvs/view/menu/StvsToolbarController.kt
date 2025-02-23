package edu.kit.iti.formal.stvs.view.menu

import edu.kit.iti.formal.stvs.logic.examples.Example
import edu.kit.iti.formal.stvs.logic.examples.ExamplesFacade
import edu.kit.iti.formal.stvs.logic.io.*
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.code.Code
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import edu.kit.iti.formal.stvs.view.Controller
import edu.kit.iti.formal.stvs.view.ViewUtils
import edu.kit.iti.formal.stvs.view.common.AlertFactory.createAlert
import edu.kit.iti.formal.stvs.view.common.FileChooserFactory
import edu.kit.iti.formal.stvs.view.common.FileChooserFactory.FileType.*
import javafx.beans.property.ObjectProperty
import javafx.collections.ListChangeListener
import javafx.collections.ObservableList
import javafx.collections.transformation.TransformationList
import javafx.scene.control.*
import org.kordamp.ikonli.Ikon
import org.kordamp.ikonli.javafx.FontIcon
import org.kordamp.ikonli.materialdesign2.MaterialDesignB
import org.kordamp.ikonli.materialdesign2.MaterialDesignC
import org.kordamp.ikonli.materialdesign2.MaterialDesignS
import org.kordamp.ikonli.materialdesign2.MaterialDesignW
import tornadofx.*
import java.io.File
import java.io.IOException


/**
 *
 * @author Alexander Weigl
 * @version 1 (21.04.24)
 */
class StvsToolbarController(private val rootModel: ObjectProperty<StvsRootModel>) : Controller {
    override val view = toolbar {
        /*
            open.accelerator = KeyCombination.keyCombination("Ctrl+o")
            saveSessionAs.accelerator = KeyCombination.keyCombination("Shift+Ctrl+s")
            saveAll.accelerator = KeyCombination.keyCombination("Ctrl+s")
            config.accelerator = KeyCombination.keyCombination("Ctrl+,")
         */
        splitmenubutton("New") {
            itemf("New Specification", ikof = MaterialDesignC.CALCULATOR_VARIANT_OUTLINE).action { createNewSpec() }
            itemf("New Code", ikof = MaterialDesignC.CODE_BRACES_BOX).action { createNewCode() }
            itemf(
                "New Session",
                ikof = MaterialDesignB.BOOK_OPEN_BLANK_VARIANT
            ).action { createNewCode(); createNewSpec() }
        }.action { createNewSpec() }

        splitmenubutton("Open", FontIcon(MaterialDesignS.STORE)) {
            itemf("Open Specification", ikof = MaterialDesignS.STORE).action { openSpec() }
            itemf("Open Code", ikof = MaterialDesignS.STORE).action { openCode() }
            itemf("Open Session", ikof = MaterialDesignS.STORE).action { openSession() }

            menu("Examples") {
                for (ex in ExamplesFacade.examples()) {
                    item(ex.name) {
                        isMnemonicParsing = true
                        //Tooltip.install(mex, Tooltip(ex.description))
                    }.action { openExample(ex) }
                }
            }

            menu("Recent files") {
                val map: ObservableList<MenuItem> = MappingList(rootModel.get().history.filenamesProperty) {
                    MenuItem(it).also { item -> item.action { doOpenFile(File(it)) } }
                }
                map.addListener(ListChangeListener<MenuItem> { _ -> items.setAll(map) })
            }
        }.action { openFile() }

        splitmenubutton("Save") {
            itemf("Save Code").action { saveCode() }
            itemf("Save Spec").action { saveSpec() }
            itemf("Save All").action { saveAll() }
            itemf("Save Session As").action { saveSessionAs() }
        }.action { saveAll() }

        button("About").action { openAboutDialog() }
        button("Preferences", graphic = FontIcon(MaterialDesignW.WRENCH_OUTLINE)).action { openConfigDialog() }
    }

    fun openExample(ex: Example) {
        val url = ex.sessionUrl
        try {
            val session: StvsRootModel = ImporterFacade.importSession(
                url.openStream(),
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

    private fun doOpenFile(file: File) {
        try {
            ImporterFacade.importFile(
                file, rootModel.get().globalConfig,
                rootModel.get().history, { hybridSpecification: HybridSpecification? ->
                    // handle hybridspecification
                    rootModel.get().hybridSpecifications
                        .add(hybridSpecification)
                }, { rootModel ->
                    // handle rootModel
                    rootModel.workingdir = file.getParentFile()
                    rootModel.filename = file.getName()
                    this.rootModel.setValue(rootModel)
                }, (ImportCodeHandler { code: Code ->
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


    private fun saveSessionAs() {
        useSaveFile(SESSION) {
            handleSaveAll(it)
            setWorkingDir(it)
        }
    }

    private fun createNewSpec() {
        rootModel.get().addNewHybridSpec()
    }

    private fun createNewCode() {
        var clear = false
        if (rootModel.get().scenario.code.sourcecode.isNotEmpty()) {
            val save = ButtonType("Save", ButtonBar.ButtonData.APPLY)
            val request = Alert(
                Alert.AlertType.CONFIRMATION, "Do you really want to throw away your code?",
                ButtonType.YES, save, ButtonType.NO
            )
            val answer = request.showAndWait()
            if (answer.isPresent) {
                if (answer.get() == save) {
                    clear = saveCode()
                }
                if (answer.get() == ButtonType.YES) {
                    clear = true
                }
            }
            if (clear) rootModel.get().scenario.code = Code()
        }
    }

    private fun openConfigDialog() {
        val dialogManager = ConfigDialogManager(
            rootModel.get().globalConfig
        )
        dialogManager.showAndWait()
    }


    private fun openAboutDialog() {
        val dialog: Dialog<*> = Dialog<Any?>()
        val pane = AboutDialogPane()
        dialog.title = "About"
        dialog.dialogPane = pane

        dialog.showAndWait()
    }

    private fun <R> useOpenFile(fileType: FileChooserFactory.FileType, block: (File) -> R): R? {
        val fileChooser = FileChooserFactory.createOpenFileChooser(fileType, rootModel.get().workingdir)
        val chosenFile = fileChooser.showOpenDialog(view.scene.window) ?: return null
        return block(chosenFile)
    }

    private fun <R> useSaveFile(fileType: FileChooserFactory.FileType, block: (File) -> R): R? {
        val fileChooser = FileChooserFactory.createSaveFileChooser(fileType, rootModel.get().workingdir)
        val chosenFile = fileChooser.showOpenDialog(view.scene.window) ?: return null
        return block(chosenFile)
    }


    private fun openCode() {
        useOpenFile(CODE) { chosenFile ->
            try {
                val code: Code = ImporterFacade.importStCode(chosenFile)
                rootModel.get().scenario.code = code
                rootModel.get().history
                    .addFilename(chosenFile.absolutePath)
                setWorkingDir(chosenFile)
            } catch (e: IOException) {
                createAlert(e).showAndWait()
            }
        }
    }

    private fun openSession() {
        useOpenFile(SESSION) { chosenFile ->
            try {
                val model: StvsRootModel = ImporterFacade.importSession(
                    chosenFile, rootModel.get().globalConfig,
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
    }

    private fun openSpec() {
        useOpenFile(SPECIFICATION) { chosenFile ->
            try {
                val spec: HybridSpecification = ImporterFacade.importHybridSpec(chosenFile)
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
    }

    private fun openFile() {
        useOpenFile(ANY) { chosenFile ->
            doOpenFile(chosenFile)
            setWorkingDir(chosenFile)
        }
    }

    private fun saveAll() {
        if (rootModel.get().filename.isEmpty()) {
            useSaveFile(SESSION) { handleSaveAll(it) }
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
                path
            )
        } catch (exception: IOException) {
            createAlert(exception).showAndWait()
        } catch (exception: ExportException) {
            createAlert(exception).showAndWait()
        }
    }

    private fun saveCode(): Boolean {
        // Set the code filename, if no filename set yet
        val code: Code = rootModel.get().scenario.code
        if (code.filename!!.isEmpty()) {
            useSaveFile(SESSION) {
                code.filename = it.absolutePath
            }
        }
        // Export the code to the file
        try {
            ExporterFacade.exportCode(code)
            return true
        } catch (e: IOException) {
            createAlert(e).showAndWait()
            return false
        }
    }

    private fun saveSpec() {
        try {
            val spec = rootModel.get().scenario.activeSpec
            if (spec == null) { // There is no active specification tab open yet
                createAlert(
                    Alert.AlertType.ERROR,
                    "Save Specification", "No specification available.", ""
                )
                    .showAndWait()
            } else {
                useSaveFile(SPECIFICATION) {
                    ExporterFacade.exportSpec(spec, ExporterFacade.ExportFormat.XML, it)
                }
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
}

fun toolbar(op: ToolBar.() -> Unit) = ToolBar().also { op(it) }

fun MenuButton.itemf(name: String, ikof: Ikon? = null, op: MenuItem.() -> Unit = {}) =
    this.item(name, graphic = ikof?.let { FontIcon(it) }, op = op)


class MappingList<E, F>(
    val origin: ObservableList<F>,
    val map: (F) -> E
) : TransformationList<E, F>(origin) {
    override fun get(index: Int): E = map(origin[index])

    override fun sourceChanged(c: ListChangeListener.Change<out F>) {
        // TODO  "Not yet implemented" i do not if necessary
    }

    override fun getSourceIndex(index: Int): Int = index
    override fun getViewIndex(index: Int): Int = index
    override val size: Int
        get() = origin.size
}