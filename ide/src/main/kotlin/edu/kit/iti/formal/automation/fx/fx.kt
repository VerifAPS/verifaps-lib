package edu.kit.iti.formal.automation.fx

import com.jfoenix.assets.JFoenixResources
import com.moandjiezana.toml.Toml
import edu.kit.iti.formal.automation.ide.ToolPane
import edu.kit.iti.formal.automation.ide.services.bufferedWriter
import edu.kit.iti.formal.util.info
import edu.kit.iti.formal.util.inputStream
import javafx.application.Application
import javafx.beans.property.SimpleBooleanProperty
import javafx.beans.property.SimpleDoubleProperty
import javafx.beans.property.SimpleObjectProperty
import javafx.beans.property.SimpleStringProperty
import javafx.collections.FXCollections
import javafx.collections.ObservableList
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.geometry.Orientation
import javafx.scene.Node
import javafx.scene.Scene
import javafx.scene.control.*
import javafx.scene.control.cell.TextFieldTreeCell
import javafx.scene.input.KeyCombination
import javafx.scene.layout.BorderPane
import javafx.scene.layout.HBox
import javafx.scene.layout.VBox
import javafx.scene.text.Font
import javafx.stage.FileChooser
import javafx.stage.Stage
import javafx.util.StringConverter
import org.kordamp.ikonli.javafx.FontIcon
import org.kordamp.ikonli.javafx.IkonResolver
import java.awt.Desktop
import java.io.File
import java.io.IOException
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*


fun main(args: Array<String>) {
    Application.launch(IdeFx::class.java, *args)
}


class IdeFx : Application() {
    val appData = ApplicationData()
    override fun start(primaryStage: Stage) {
        appData.load(ConfigurationPaths.appDataPath)

        val main = MainScene(appData)
        main.scene.stylesheets.addAll(
            JFoenixResources.load("css/jfoenix-fonts.css").toExternalForm(),
            JFoenixResources.load("css/jfoenix-design.css").toExternalForm(),
            javaClass.getResource("/css/style.css").toExternalForm()
        )
        primaryStage.scene = main.scene

        primaryStage.x = appData.posX.value
        primaryStage.y = appData.posY.value
        primaryStage.width = appData.windowWidth.value
        primaryStage.height = appData.windowHeight.value

        appData.posX.bind(primaryStage.xProperty())
        appData.posY.bind(primaryStage.yProperty())
        appData.windowWidth.bind(primaryStage.widthProperty())
        appData.windowHeight.bind(primaryStage.heightProperty())


        primaryStage.title = "VERIFAPS IDE"
        primaryStage.show()
    }

    override fun stop() {
         appData.store(ConfigurationPaths.appDataPath)
    }
}

interface Controller {
    val ui: Node
}

object ConfigurationPaths {
    val operationSystem by lazy {
        val os = System.getProperty("os.name")
        when {
            os.contains("Mac") -> "mac"
            os.contains("Windows") -> "win"
            os.contains("Linux") -> "lin"
            else -> ""
        }
    }

    val applicationName = "verifaps-fx"

    val configFolder by lazy {
        val home = System.getProperty("user.home")
        val p = when (operationSystem) {
            "mac" -> Paths.get(home, "Library", "Application Support", applicationName)
            "win" -> {
                val version = System.getProperty("os.version")
                Paths.get(System.getenv("APPDATA"), applicationName)
            }
            "lin" -> {
                Paths.get(home, ".config", applicationName)
            }
            else -> Paths.get(applicationName)
        }
        Files.createDirectories(p)
        info("Configuration folder: $p")
        p
    }

    val appDataPath by lazy {
        configFolder.resolve("config.properties")
    }

    val recentFiles by lazy {
        configFolder.resolve("recentfiles")
    }
}

class ApplicationData {
    val posX = SimpleDoubleProperty(this, "posX", 10.0)
    val posY = SimpleDoubleProperty(this, "posX", 10.0)
    val windowHeight = SimpleDoubleProperty(this, "windowHeight", 400.0)
    val windowWidth = SimpleDoubleProperty(this, "windowWidth", 600.0)
    val maximized = SimpleBooleanProperty(this, "maximized", false)
    val lastNavigatorPath = SimpleStringProperty(this, "lastNavigatorPath", File(".").absolutePath)

    fun load(path: Path) {
        try {
            val p = Properties()
            path.inputStream().use {
                p.load(it)
            }
            posX.value = p["posX"].toString().toDouble()
            posY.value = p["posY"].toString().toDouble()
            windowHeight.value = p["windowHeight"].toString().toDouble()
            windowWidth.value = p["windowWidth"].toString().toDouble()
            maximized.value = p["maximized"] == "true"
            lastNavigatorPath.value = p["lastNavigatorPath"]?.toString()
        }catch (e : IOException) {
            info(e.message.toString())
        }
    }

    fun store(path: Path) {
        val p = Properties()
        p["posX"] = posX.value
        p["posY"] = posY.value
        p["windowHeight"] = windowHeight.value
        p["windowWidth"] = windowWidth.value
        p["maximized"] = maximized.value
        p["lastNavigatorPath"] = lastNavigatorPath.value
        path.bufferedWriter().use {
            p.store(it, "")
        }
    }
}

class MainScene(val appData: ApplicationData) {
    val config by lazy {
        val stream = javaClass.getResourceAsStream("/config.toml")
        require(stream != null)
        val s = Toml().read(stream)
        //s.entrySet().forEach { (a,b)-> println("$a :$b") }
        s
    }

    //region controllers
    val root = BorderPane()
    val menu = IdeMenu(this)
    val fileNavigator = FileNavigator(this)
    val outline = FileOutline()
    //endregion

    val scene = Scene(root, 300.0, 300.0)

    val left = SplitPane()
    val center = SplitPane()
    val editorTabPanes = arrayListOf(createEditorTabPane())
    val statusBar = Label("")
    val openEditors = arrayListOf<Editor>()

    init {
        root.top = menu.ui
        root.center = center
        left.items.setAll(outline.ui, fileNavigator.ui)
        left.orientation = Orientation.VERTICAL
        center.items.add(left)
        center.items.addAll(editorTabPanes)

        if(appData.lastNavigatorPath.value!=null)
            fileNavigator.rootFile.value = Paths.get(appData.lastNavigatorPath.value)

    }

    fun publishMessage(status: String, graphic: Node? = null) {
        statusBar.text = status
        statusBar.graphic = graphic
    }

    private fun createEditorTabPane(): TabPane {
        return TabPane()
    }

    fun createCodeEditor() {
        addEditorTab(Editor())
    }

    fun addEditorTab(editor: Editor) {
        val tabPanel = editorTabPanes.first()
        val tab = Tab(editor.title.value, editor.ui)
        tabPanel.tabs.add(tab)
        editor.title.addListener { _, _, new -> tab.text = new }
        openEditors.add(editor)
        editor.ui.focusedProperty().addListener { obs, _, new -> if (new) currentEditor.value = editor }
        currentEditor.value = editor
        editor.ui.requestFocus()
    }

    /*
    val recentFiles by lookup.with<RecentFilesService>()
    val actionClearRecentFiles = createAction(
        "Clear recent files",
        "File.Recent Files", prio = 5
    ) {
        recentFiles.clear()
        refreshRecentFiles()
    }

    val actionTranslateSfc = createAction(
        "Translate all Sfc to St code",
        "Tools"
    ) {
        currentEditor?.also {
            val file = File(
                it.file?.parentFile, it.file?.nameWithoutExtension +
                        "_translated." + it.file?.extension
            )
            val elements = IEC61131Facade.file(CharStreams.fromString(it.text))
            IEC61131Facade.translateSfcToSt(elements)
            file.bufferedWriter().use {
                IEC61131Facade.printTo(it, elements, true)
            }
            open(file)
        }
    }*/

    val recentFiles = FXCollections.observableArrayList<File>()

    val currentEditor = SimpleObjectProperty<Editor>(this, "currentEditor", null)

    fun runCurrentProgram() {
        currentEditor.value?.let {
            /*val runnerWindow = RunnerWindow(lookup, it)
                addToolTab(runnerWindow)*/
        }
    }

    fun close() {}

    fun saveAs(editor: Editor? = currentEditor.value) =
        editor?.also {
            val fileChooser = FileChooser()
            fileChooser.showSaveDialog(scene.window)?.let { new ->
                editor.filename.value = new
                save(editor)
            }
        }

    fun save(editor: Editor? = currentEditor.value) {
        editor?.also { editor ->
            editor.filename.value?.also { filename ->
                filename.writeText(editor.ui.text)
            }
        }
    }

    fun open() {
        val fc = FileChooser()
        fc.showOpenDialog(scene.window)?.let { file ->
            open(file)
        }
    }


    fun open(f: File) {
        if (f !in recentFiles) {
            recentFiles.add(f)
        }
        val editor = Editor()
        editor.filename.value = f
        editor.ui.insertText(0, f.readText())
        addEditorTab(editor)
    }

    fun editorToTheRight(editor: Editor? = currentEditor.value) {
        if (editor == null) return
        val tabPane = editorTabPanes.find { it.tabs.any { tab -> tab.content == editor.ui } }
        if (tabPane != null) {
            val tabIndex = editorTabPanes.indexOf(tabPane)
            if (tabPane == editorTabPanes.last()) {
                TabPane().also { editorTabPanes.add(it); center.items.add(it) }
            }
            val target = editorTabPanes[tabIndex + 1]
            val tab = tabPane.tabs.find { it.content == editor.ui }!!
            tabPane.tabs.remove(tab)
            target.tabs.add(tab)
        }
    }

    fun editorToTheLeft(editor: Editor? = currentEditor.value) {
        val tabPane = editorTabPanes.find { it.tabs.any { it.content == editor } }
        if (tabPane != null) {
            val tabIndex = editorTabPanes.indexOf(tabPane)
            if (tabPane == editorTabPanes.first()) {
                TabPane().also { editorTabPanes.add(0, it) }
            }
            val target = editorTabPanes[tabIndex - 1]
            val tab = tabPane.tabs.find { it.content == editor }!!
            tabPane.tabs.remove(tab)
            target.tabs.add(tab)
        }
    }

    fun addToolTab(window: ToolPane) {
    }


    internal fun getValue(key: String): String? = config.getString("actions.$key") ?: null.also {
        System.err.println("actions.$key is not defined in config")
    }

    internal fun createItem(id: String, function: (ActionEvent) -> Unit): MenuItem {
        val resolver = IkonResolver.getInstance()
        val name = getValue("$id.name") ?: id
        val icon = getValue("$id.icon")?.let { ref ->
            resolver.resolve(ref).resolve(ref)?.let { FontIcon(it) }
        }
        val accel = getValue("$id.accel")?.let { KeyCombination.keyCombination(it) }
        val mi = MenuItem(name, icon)
        mi.onAction = EventHandler(function)
        mi.accelerator = accel
        return mi
    }
}

internal fun createHeaderLabel(text: String) = Label(text).also {
    it.font = Font(it.font.name, it.font.size + 6)
}

class IdeMenu(val root: MainScene) {
    val file = Menu("File")
    val edit = Menu("Edit")
    val view = Menu("View")
    val tools = Menu("Tools")

    val recentFiles = Menu("Recent files")

    val actionSaveAs = root.createItem("save-as") { root.saveAs() }
    val actionSave = root.createItem("save") { root.save() }
    val actionNew = root.createItem("new") { root.createCodeEditor() }
    val actionRun = root.createItem("run") { root.runCurrentProgram() }
    val actionOpen = root.createItem("open") { root.open() }
    val actionClose = root.createItem("close") { root.close() }
    val actionIncrFontSize = root.createItem("incr-font-size") {}
    val actionDecrFontSize = root.createItem("decr-font-size") {}
    val actionMoveEditorToLeft = root.createItem("editor-move-left") { root.editorToTheLeft() }
    val actionMoveEditorToRight = root.createItem("editor-move-right") { root.editorToTheRight() }


    val ui = MenuBar(file, edit, view, tools)

    init {
        file.items.setAll(
            actionNew,
            actionOpen,
            recentFiles,
            SeparatorMenuItem(),
            actionSave,
            actionSaveAs,
            SeparatorMenuItem(),
            actionClose,
        )
        view.items.setAll(
            actionIncrFontSize,
            actionDecrFontSize,
            SeparatorMenuItem(),
            actionMoveEditorToLeft,
            actionMoveEditorToRight
        )
        tools.items.setAll(actionRun)
    }
}

abstract class TitledPanel(header: String) {
    val ui
        get() = root
    val root = BorderPane()
    val buttonBox = HBox()
    abstract val main: Node

    init {
        root.top = VBox(createHeaderLabel(header), buttonBox, Separator())
        root.center = main
    }
}

class FileNavigator(main: MainScene) : TitledPanel("Navigator") {
    val rootFile = SimpleObjectProperty(
        this, "rootFile",
        Paths.get(".").normalize().toAbsolutePath()
    )
    val treeFile = TreeView(SimpleFileTreeItem(rootFile.value))
    override val main: Node
        get() = treeFile

    val contextMenu: ContextMenu = ContextMenu()

    private fun markFolderUnderMouse(event: ActionEvent) {
    }

    private val actionOpenFile = main.createItem("tree-open-file") {
        markFolderUnderMouse(it)
        treeFile.selectionModel.selectedItem?.let {
            main.open(it.value.toFile())
        }
    }


    private val actionNewFile = main.createItem("tree-new-file") {
        markFolderUnderMouse(it)
        treeFile.selectionModel.selectedItem?.let { item ->
            val path = item.value!!
            val dialog = TextInputDialog()
            dialog.contentText = "File name:"
            val name = dialog.showAndWait()
            name.ifPresent {
                val newFile = path.resolve(it)
                try {
                    Files.createFile(newFile)
                    main.open(newFile.toFile())
                    refresh()
                } catch (e: IOException) {
                    val a = Alert(Alert.AlertType.ERROR)
                    a.contentText = e.message
                    a.show()
                }
            }
        }
    }
    private val actionNewDirectory = main.createItem("tree-new-directory") {
        markFolderUnderMouse(it)
        treeFile.selectionModel.selectedItem?.let { item ->
            val path = item.value!!
            val dialog = TextInputDialog()
            dialog.contentText = "Folder name:"
            val name = dialog.showAndWait()
            name.ifPresent {
                val newFile = path.resolve(it)
                try {
                    Files.createDirectory(newFile)
                    main.open(newFile.toFile())
                    refresh()
                } catch (e: IOException) {
                    val a = Alert(Alert.AlertType.ERROR)
                    a.contentText = e.message
                    a.show()
                }
            }
        }
    }
    private val actionRenameFile = main.createItem("tree-rename-file") { }
    private val actionDeleteFile = main.createItem("tree-delete-file") {}
    private val actionGoUp = main.createItem("go-up") {
        markFolderUnderMouse(it)
        (treeFile.root.value as? Path)?.let { file ->
            treeFile.root = SimpleFileTreeItem(file.parent.toAbsolutePath())
            treeFile.root.isExpanded = true
        }
    }
    private val actionGoInto = main.createItem("go-into") {
        markFolderUnderMouse(it)
        (treeFile.selectionModel.selectedItem)?.let { file ->
            treeFile.root = SimpleFileTreeItem(file.value.toAbsolutePath())
            treeFile.root.isExpanded = true
        }
    }
    private val actionRefresh = main.createItem("refresh") { refresh() }

    private fun refresh() {}

    private val actionExpandSubTree = main.createItem("expand-tree") {
        markFolderUnderMouse(it)
    }
    private val actionOpenExplorer = main.createItem("open-in-explorer") {
        markFolderUnderMouse(it)
        (treeFile.selectionModel.selectedItem)?.let { file ->
            try {
                Desktop.getDesktop()?.browseFileDirectory(file.value.toFile())
            } catch (e: UnsupportedOperationException) {
                ProcessBuilder("explorer", "/select,${file.value}").start()
            }
        }
    }

    private val actionOpenSystem = main.createItem("xdg-open") {
        markFolderUnderMouse(it)
        (treeFile.selectionModel.selectedItem)?.let { file ->
            try {
                Desktop.getDesktop()?.open(file.value.toFile())
            } catch (e: UnsupportedOperationException) {
                ProcessBuilder("explorer", "/select,${file.value}").start()
            }
        }
    }

    init {
        contextMenu.items.setAll(
            actionOpenFile,
            SeparatorMenuItem(),
            actionNewFile,
            actionNewDirectory,
            actionRenameFile,
            actionDeleteFile,
            SeparatorMenuItem(),
            actionGoUp,
            actionGoInto,
            SeparatorMenuItem(),
            actionExpandSubTree,
            actionRefresh,
            SeparatorMenuItem(),
            actionOpenExplorer,
            actionOpenSystem
        )


        treeFile.contextMenu = contextMenu
        treeFile.isEditable = false
        treeFile.isShowRoot = true
        rootFile.addListener { _, _, new ->
            treeFile.root = SimpleFileTreeItem(new)
        }
        root.center = treeFile
        treeFile.setCellFactory { tv ->
            TextFieldTreeCell(object : StringConverter<Path>() {
                override fun toString(obj: Path?): String = obj?.fileName.toString() ?: ""
                override fun fromString(string: String?): Path = Paths.get(string)
            })
        }
        treeFile.root.isExpanded = true
    }
}

class SimpleFileTreeItem(f: Path) : TreeItem<Path>(f) {
    private var isFirstTimeChildren = true
    private var isFirstTimeLeaf = true
    private var isLeaf = false

    override fun getChildren(): ObservableList<TreeItem<Path>> {
        if (isFirstTimeChildren) {
            isFirstTimeChildren = false
            super.getChildren().setAll(buildChildren(this))
        }
        return super.getChildren()
    }

    override fun isLeaf(): Boolean {
        if (isFirstTimeLeaf) {
            isFirstTimeLeaf = false
            val f = value as Path
            isLeaf = Files.isRegularFile(f)
        }
        return isLeaf
    }

    private fun buildChildren(node: TreeItem<Path>): ObservableList<TreeItem<Path>> {
        val f = node.value
        if (f != null && Files.isDirectory(f)) {
            val children: ObservableList<TreeItem<Path>> = FXCollections.observableArrayList()
            Files.list(f).forEach {
                children.add(SimpleFileTreeItem(it))
            }
            return children
        }
        return FXCollections.emptyObservableList()
    }
}


class FileOutline : TitledPanel("Outline") {
    val outlineTree = TreeView<Any>()

    init {
    }

    override val main: Node
        get() {
            return outlineTree
        }
}
