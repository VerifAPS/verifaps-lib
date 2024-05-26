package edu.kit.iti.formal.automation.fx

import edu.kit.iti.formal.fxutils.group
import edu.kit.iti.formal.fxutils.item
import edu.kit.iti.formal.fxutils.ribbon
import edu.kit.iti.formal.fxutils.tab
import edu.kit.iti.formal.util.info
import javafx.application.Platform
import javafx.beans.property.SimpleObjectProperty
import javafx.collections.FXCollections
import javafx.geometry.Side
import javafx.scene.Node
import javafx.scene.control.MenuItem
import javafx.scene.control.Tab
import javafx.scene.control.TabPane
import javafx.scene.paint.Color
import javafx.scene.text.FontWeight
import javafx.stage.FileChooser
import javafx.stage.Stage
import tornadofx.*
import java.io.File
import java.nio.file.Files
import java.nio.file.Paths

object Main {
    @JvmStatic
    fun main(args: Array<String>) {
        launch<IdeFx>(*args)
    }
}

class IdeStyle : Stylesheet() {
    companion object {
        val styleTextArea by cssclass("styled-text-area")
        val text by cssclass()
        val errorChar by cssclass("error-char")
        val structural by cssclass()
        val literal by cssclass()
        val identifier by cssclass()
        val fancyIdentifier by cssclass("fancy-identifier")
        val comment by cssclass()
        val datatype by cssclass()
        val control by cssclass()
        val operators by cssclass()
    }

    init {
        val base03 = Color.web("#002b36")
        val base02 = Color.web("#073642")
        val base01 = Color.web("#586e75")
        val base00 = Color.web("#657b83")
        val base0 = Color.web("#839496")
        val base1 = Color.web("#93a1a1")
        val base2 = Color.web("#eee8d5")
        val base3 = Color.web("#fdf6e3")
        val yellow = Color.web("#b58900")
        val orange = Color.web("#cb4b16")
        val red = Color.web("#dc322f")
        val magenta = Color.web("#d33682")
        val violet = Color.web("#6c71c4")
        val blue = Color.web("#268bd2")
        val cyan = Color.web("#2aa198")
        val green = Color.web("#859900")

        styleTextArea {
            text {
                backgroundColor += base03
            }
        }

        errorChar {
            backgroundColor += red
        }

        error {
            fontWeight = FontWeight.BOLD
            backgroundColor += red
        }

        separator {
            //fill =
        }

        structural {
            fill = blue
            fontWeight = FontWeight.BOLD
        }

        literal {
            fill = violet
        }

        identifier {
            //fill = c(" #b58900")
        }

        fancyIdentifier {
            fill = magenta
            fontWeight = FontWeight.BOLD
        }

        comment {
            fill = base01
        }

        datatype {
            fill = blue
        }

        control {
            fill = blue
        }

        operators {
            fill = orange
        }
    }
}


class IdeFx : App(IdeView::class, IdeStyle::class) {
    init {
        //reloadStylesheetsOnFocus()
        //dumpStylesheets()

    }

    override fun start(stage: Stage) {
        super.start(stage)
        //val theme = TransitTheme(stage.scene, Style.LIGHT);
        //theme.reApplyTheme()
    }
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

class IdeView : View("VERIFAPS IDE") {
    val recentFiles = FXCollections.observableArrayList<File>().also { seq ->
        config.jsonArray("recentFiles")
            ?.map { File(it.toString()) }
            ?.forEach { seq.add(it) }
    }

    val currentEditor = SimpleObjectProperty<Editor>(this, "currentEditor", null)


    //region controllers
    val menu = IdeMenu(this)
    val fileNavigator = FileNavigator(this)
    val outline = FileOutline()
    val issues = Issues()

    val left = drawer(multiselect = true, floatingContent = false) {
        item("Navigator", expanded = false, showHeader = true) {
            this.add(outline.root)
        }
        item("Files", expanded = true, showHeader = true) {
            this.add(fileNavigator.root)
        }
    }
    val bottom = drawer(Side.BOTTOM, multiselect = false, floatingContent = false) {
        item("Issues") { add(Issues::class) }
        item("Table Preview") { add(TTPreview::class) }
    }
    val blubber = drawer(Side.RIGHT, multiselect = false, floatingContent = false) {
        item("Geteta") { add(Geteta::class) }
        item("Reteta") { add(Reteta::class) }
    }
    val center = splitpane()

    override val root = borderpane {
        top = menu.root
        center = this@IdeView.center
        left = this@IdeView.left
        bottom = this@IdeView.bottom
        right = this@IdeView.blubber
    }
    //endregion

    val statusBar = label("")
    val editorTabPanes = arrayListOf(createEditorTabPane())
    val openEditors = arrayListOf<Editor>()

    init {
        center.items.addAll(editorTabPanes)
        //if (appData.lastNavigatorPath.value != null)
        //    fileNavigator.rootFile.value = Paths.get(appData.lastNavigatorPath.value)
        subscribe<StatusMessage> { publishMessage(it.text, it.graphic) }
        Platform.runLater {
            open(File("geteta/examples/NewFile.gtt").absoluteFile)
        }
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
        val tab = Tab(editor.editorTitle.value, editor.root)
        tabPanel.tabs.add(tab)
        editor.editorTitle.addListener { _, _, new -> tab.text = new }
        openEditors.add(editor)
        editor.root.focusedProperty().addListener { obs, _, new -> if (new) currentEditor.value = editor }
        currentEditor.value = editor
        editor.root.requestFocus()
    }

    fun saveAs(editor: Editor? = currentEditor.value) =
        editor?.also {
            val fileChooser = FileChooser()
            fileChooser.showSaveDialog(currentWindow)?.let { new ->
                editor.filenameProperty.value = new
                save(editor)
            }
        }

    fun save(editor: Editor? = currentEditor.value) {
        editor?.also { editor ->
            editor.filenameProperty.value?.also { filename ->
                filename.writeText(editor.root.text)
            }
        }
    }

    fun open() {
        val fc = FileChooser()
        fc.showOpenDialog(currentWindow)?.let { file ->
            open(file)
        }
    }


    fun open(f: File) {
        if (f !in recentFiles) {
            recentFiles.add(f)
        }
        val editor = Editor()
        editor.filenameProperty.value = f
        editor.root.insertText(0, f.readText())
        addEditorTab(editor)
    }

    fun editorToTheRight(editor: Editor? = currentEditor.value) {
        if (editor == null) return
        val tabPane = editorTabPanes.find { it.tabs.any { tab -> tab.content == editor.root } }
        if (tabPane != null) {
            val tabIndex = editorTabPanes.indexOf(tabPane)
            if (tabPane == editorTabPanes.last()) {
                TabPane().also { editorTabPanes.add(it); center.items.add(it) }
            }
            val target = editorTabPanes[tabIndex + 1]
            val tab = tabPane.tabs.find { it.content == editor.root }!!
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
}

class StatusMessage(val text: String, val graphic: Node? = null) : FXEvent()

class IdeMenu(val ide: IdeView) : View() {
    lateinit var recentFiles: MenuItem

    override val root =
        vbox {
            menubar {
                menu("File") {
                    item("New", "ctrl-n", null, ide::createCodeEditor)
                    item("Open", "ctrl-o", "fas-folder-open", ide::open)
                    val recentFiles = item("Recent files")
                    separator()
                    item("Save", "ctrl-s", "far-save", ide::save)
                    item("Save As...", "ctrl-shift-s", "fas-save", ide::saveAs)
                    separator()
                    item("Close", null, null, ide::close)
                }
                menu("Edit") {}
                menu("View") {
                    item("Larger texts", "ctrl-PLUS", "fas-folder-open") {}
                    item("Smaller texts", "ctrl-MINUS", "fas-folder-open") {}
                    separator()
                    item("Editor to Left", "ctrl-LEFT", null, ide::editorToTheLeft)
                    item("Editor to Right", "ctrl-RIGHT", null, ide::editorToTheRight)
                }
                menu("Tools") {
                    item("Translate SFC to ST", null, null) {
                        /*currentEditor?.also {
                    val file = File(
                        it.file?.parentFile, it.file?.nameWithoutExtension +
                                "_translated." + it.file?.extension
                    )
                    val elements = IEC61131Facade.file(CharStreams.fromString(it.text))
                    IEC61131Facade.translateSfcToSt(elements)
                    file.bufferedWriter().use {
                        IEC61131Facade.printTo(it, elements, true)
                    }
                    open(file)*/
                    }
                }
            }

            ribbon {
                tab("test") {
                    group("File") {
                        item("New", "ctrl-n", null, event = ide::createCodeEditor)
                        item("Open", "ctrl-o", "fas-folder-open", event = ide::open)
                        //val recentFiles = item("Recent files")
                        item("Save", "ctrl-s", "far-save", event = ide::save)
                        item("Save As...", "ctrl-shift-s", "fas-save", event = ide::saveAs)
                        item("Close", null, null, event = ide::close)
                    }
                    group("Edit") {}
                    group("View") {
                        item("Larger texts", "ctrl-PLUS", "fas-folder-open") {}
                        item("Smaller texts", "ctrl-MINUS", "fas-folder-open") {}
                        item("Editor to Left", "ctrl-LEFT", null, event = ide::editorToTheLeft)
                        item("Editor to Right", "ctrl-RIGHT", null, event = ide::editorToTheRight)
                    }
                    group("Tools") {
                        item("Translate SFC to ST", null, null) {
                            /*currentEditor?.also {
                        val file = File(
                            it.file?.parentFile, it.file?.nameWithoutExtension +
                                    "_translated." + it.file?.extension
                        )
                        val elements = IEC61131Facade.file(CharStreams.fromString(it.text))
                        IEC61131Facade.translateSfcToSt(elements)
                        file.bufferedWriter().use {
                            IEC61131Facade.printTo(it, elements, true)
                        }
                        open(file)*/
                        }
                    }
                }
            }
        }
}
