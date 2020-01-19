package edu.kit.iti.formal.automation.ide

import bibliothek.gui.dock.common.CControl
import bibliothek.gui.dock.common.CGrid
import bibliothek.gui.dock.common.intern.CDockable
import bibliothek.gui.dock.common.intern.DefaultCommonDockable
import bibliothek.gui.dock.control.focus.DefaultFocusRequest
import bibliothek.gui.dock.util.Priority
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.ide.editors.STFoldParser
import edu.kit.iti.formal.automation.ide.editors.TTFolderParser
import edu.kit.iti.formal.automation.ide.services.*
import edu.kit.iti.formal.automation.ide.tools.*
import edu.kit.iti.formal.automation.st.ast.Position
import edu.kit.iti.formal.util.inputStream
import org.antlr.v4.runtime.CharStreams
import org.fife.rsta.ui.GoToDialog
import org.fife.rsta.ui.search.FindDialog
import org.fife.rsta.ui.search.ReplaceDialog
import org.fife.rsta.ui.search.SearchEvent
import org.fife.rsta.ui.search.SearchListener
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea
import org.fife.ui.rsyntaxtextarea.folding.FoldParserManager
import org.fife.ui.rtextarea.SearchEngine
import org.fife.ui.rtextarea.SearchResult
import java.awt.*
import java.awt.event.KeyEvent
import java.awt.event.WindowAdapter
import java.awt.event.WindowEvent
import java.io.DataInputStream
import java.io.File
import java.text.ParseException
import java.util.*
import javax.swing.*
import javax.swing.text.BadLocationException
import kotlin.properties.Delegates

/**
 *
 * @author Alexander Weigl
 * @version 1 (10.03.19)
 */
class Ide(val lookup: Lookup, vararg initialFiles: File) : JFrame(),
        GetFileChooser, FileOpen,
        TabManagement, ActionService, JumpService, StatusService {

    val editorFactory by lookup.with<EditorFactory>()
    val configurationPaths = lookup.get<ConfigurationPaths>()
    val appConfiguration = lookup.get<ApplicationConfiguration>()

    private var fontSize: Float by Delegates.observable(12f) { prop, _, new ->
        if (fontSize < 6f) fontSize = 6f
        else {
            defaultFont = defaultFont.deriveFont(new)
            jMenuBar.font = jMenuBar.font.deriveFont(new)
            lookup.get<Colors>().defaultFont = defaultFont
        }
    }

    var defaultFont by Delegates.observable(Font(Font.MONOSPACED, Font.PLAIN, 12)) { _, _, new ->
        lookup.getAll<CodeEditor>().forEach {
            // it.textFont = new
        }
    }

    val currentEditor: CodeEditor?
        get() = currentTabbedPanel?.dockable as? CodeEditor

    val currentTabbedPanel: DefaultCommonDockable?
        get() = globalPort.controller?.focusedDockable as? DefaultCommonDockable

    override val fileChooser = JFileChooser()
    val defaultToolBar = JToolBar()

    val actions = arrayListOf<IdeAction>()

    val actionSaveAs = createAction(name = "Save As", menuPath = "File", prio = 3,
            fontIcon = FontAwesomeSolid.SAVE) { saveAs() }
    val actionSave = createAction("Save", "File",
            KeyStroke.getKeyStroke(KeyEvent.VK_S, KeyEvent.CTRL_DOWN_MASK), 2,
            fontIcon = FontAwesomeRegular.SAVE) { save() }
    val actionNew = createAction("New", "File",
            KeyStroke.getKeyStroke(KeyEvent.VK_N, KeyEvent.CTRL_DOWN_MASK), 0,
            fontIcon = FontAwesomeRegular.FILE) { createCodeEditor() }
    val actionRun = createAction(name = "Run", menuPath = "Tools", prio = 9,
            fontIcon = FontAwesomeSolid.RUNNING) { runCurrentProgram() }

    private fun createCodeEditor() {
        val editor = CodeEditor(lookup, lookup.get<DockableCodeEditorFactory>())
        addEditorTab(editor)
    }

    val actionOpen = createAction("Open", "File",
            KeyStroke.getKeyStroke(KeyEvent.VK_O, KeyEvent.CTRL_DOWN_MASK), 1,
            fontIcon = FontAwesomeRegular.FOLDER_OPEN) { open() }
    val actionClose = createAction("Close", "File",
            KeyStroke.getKeyStroke(KeyEvent.VK_Q, KeyEvent.CTRL_DOWN_MASK), 4,
            fontIcon = FontAwesomeSolid.WINDOW_CLOSE) { close() }
    val actionIncrFontSize = createAction("Increase Font Size", "View",
            KeyStroke.getKeyStroke(KeyEvent.VK_PLUS, KeyEvent.CTRL_DOWN_MASK),
            fontIcon = FontAwesomeSolid.PLUS) { ++fontSize }
    val actionDecrFontSize = createAction("Decrease Font Size", "View",
            KeyStroke.getKeyStroke(KeyEvent.VK_MINUS, KeyEvent.CTRL_DOWN_MASK),
            fontIcon = FontAwesomeSolid.MINUS) { --fontSize }


    val recentFiles by lookup.with<RecentFilesService>()
    val actionClearRecentFiles = createAction("Clear recent files",
            "File.Recent Files", prio = 5) {
        recentFiles.clear()
        refreshRecentFiles()
    }

    val actionTranslateSfc = createAction("Translate all Sfc to St code",
            "Tools") {
        currentEditor?.also {
            val file = File(it.file?.parentFile, it.file?.nameWithoutExtension +
                    "_translated." + it.file?.extension)
            val elements = IEC61131Facade.file(CharStreams.fromString(it.text))
            IEC61131Facade.translateSfc(elements)
            file.bufferedWriter().use {
                IEC61131Facade.printTo(it, elements, true)
            }
            open(file)
        }
    }

    val lblStatus = JLabel()
    val statusBar = Box(BoxLayout.X_AXIS).also {
        it.add(lblStatus)
    }

    override fun publishMessage(status: String) {
        lblStatus.text = status
    }

    private fun runCurrentProgram() {
        currentEditor?.let {
            try {
                val runnerWindow = RunnerWindow(lookup, it)
                addToolTab(runnerWindow)
            } catch (e: ParseException) {
            }
        }
    }


    val editingDialogs = EditingDialogsImpl(this)

    val actionShowFindDialog = createAction("Find...", "Edit",
            accel = KeyStroke.getKeyStroke("ctrl shift typed f")) {
        currentEditor?.let {
            editingDialogs.openSearchDialog(it)
        }
    }
    val actionShowReplaceDialog = createAction("Replace...", "Edit",
            accel = KeyStroke.getKeyStroke("ctrl shift typed r")) {
        currentEditor?.let {
            editingDialogs.openReplaceDialog(it)
        }
    }

    var globalPort = CControl()

    init {
        lookup.register<GetFileChooser>(this)
        lookup.register<FileOpen>(this)
        lookup.register<ProblemList>(ProblemList())
        lookup.register<JumpService>(this)
        lookup.register<EditingDialogs>(editingDialogs)

        globalPort.controller.icons.also {
            val p = Priority.CLIENT

            it.setIcon("locationmanager.normalize", p,
                    IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_RESTORE, 12f))

            it.setIcon("locationmanager.maximize", p,
                    IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_MAXIMIZE, 12f))

            it.setIcon("locationmanager.minimize", p,
                    IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_MINIMIZE, 12f))

            it.setIcon("locationmanager.externalize", p,
                    IconFontSwing.buildIcon(FontAwesomeSolid.EXTERNAL_LINK_SQUARE_ALT, 12f))

            it.setIcon("locationmanager.unexternalize", p,
                    IconFontSwing.buildIcon(FontAwesomeSolid.MOUSE_POINTER, 12f))

            it.setIcon("locationmanager.unmaximize_externalized", p,
                    IconFontSwing.buildIcon(FontAwesomeSolid.EXTERNAL_LINK_ALT, 12f))

            it.setIcon("screen.maximize", p,
                    IconFontSwing.buildIcon(FontAwesomeRegular.EDIT, 12f))

            it.setIcon("close", p,
                    IconFontSwing.buildIcon(FontAwesomeRegular.WINDOW_CLOSE, 12f))


//            setIcon("replace", p,
//                    IconFontSwing.buildIcon(FontAwesomeRegular., 12f))
        }

        globalPort.addMultipleDockableFactory("codeEditor", lookup.get<DockableCodeEditorFactory>())

        defaultToolBar.add(actionNew)
        defaultToolBar.add(actionOpen)
        defaultToolBar.add(actionSave)
        defaultToolBar.add(actionClose)

        title = "IEC61131  Ide"
        iconImage = IconFontSwing.buildImage(FontAwesomeSolid.PENCIL_RULER, 16f)
        defaultCloseOperation = EXIT_ON_CLOSE
        contentPane.layout = BorderLayout(5, 5)
        contentPane.add(defaultToolBar, BorderLayout.NORTH)
        contentPane.add(globalPort.contentArea, BorderLayout.CENTER)
        contentPane.add(statusBar, BorderLayout.SOUTH)

        jMenuBar = JMenuBar()
        val actions = listOf(
                actionNew,
                actionTranslateSfc,
                actionShowFindDialog,
                actionShowReplaceDialog,
                actionSaveAs,
                actionRun,
                actionSave,
                actionOpen,
                actionClose,
                actionIncrFontSize,
                actionDecrFontSize)
        actions.sortedBy { it.priority }
                .forEach { jMenuBar import it }
        refreshRecentFiles()

        val tree = FileTreePanel(lookup)
        val overview = OverviewPanel(lookup)
        lookup.register<OutlineService>(overview)
        lookup.register<NavigatorService>(tree)

        val getetaPreview = GetetaPreview(lookup)
        val tools = arrayOf(
                getetaPreview,
                GetetaWindow(lookup),
                RetetaWindow(lookup),
                ProblemPanel(lookup))

        lookup.register<GetetaPreviewService>(getetaPreview)

        if (configurationPaths.layoutFile.exists()) {
            globalPort.read(DataInputStream(configurationPaths.layoutFile.inputStream()))
            globalPort.addDockable(tree)
            globalPort.addDockable(overview)
            tools.forEach { globalPort.addDockable(it) }
            globalPort.load("STARTUP")
        } else {
            val grid = CGrid(globalPort)
            grid.add(0.0, 0.0, 0.3, 0.5, overview)
            grid.add(0.0, 0.5, 0.3, 0.5, tree)
            if (initialFiles.isEmpty()) {
                val editor = editorFactory.get(File("scratch.st"))
                grid.add(1.0, 0.0, 5.0, 4.0, editor)
            } else {
                val docks = initialFiles.mapNotNull(editorFactory::get)
                docks.forEach(lookup::register)

                grid.add(1.0, 0.0, 5.0, 4.0,
                        *(docks.map { it }.toTypedArray()))
            }

            grid.add(1.0, 4.0, 5.0, 1.0, *tools)
            globalPort.contentArea.deploy(grid)
        }

        size = Dimension(appConfiguration.windowWidth, appConfiguration.windowWidth)
        location.x = appConfiguration.posX
        location.y = appConfiguration.posY


        addWindowListener(object : WindowAdapter() {
            override fun windowClosing(e: WindowEvent?) {
                appConfiguration.windowWidth = size.width
                appConfiguration.windowHeight = size.height
                appConfiguration.posX = location.x
                appConfiguration.posY = location.y
                //appConfiguration.maximized =
            }
        })

        invalidate()
        revalidate()
        revalidate()
        repaint()
        repaint()

        Runtime.getRuntime().addShutdownHook(Thread {
            globalPort.save("STARTUP")
            globalPort.write(configurationPaths.layoutFile.toFile())
        })

        publishMessage("Welcome!")
    }

    override fun registerAction(act: IdeAction) {
        actions += act
        addActionIntoMenubar(act)
        addActionIntoToolbar(act)
    }

    private fun addActionIntoToolbar(act: IdeAction) {
        if (act.toolbarId == null) {
            defaultToolBar.add(act)
        }
    }

    override fun deregisterAction(act: IdeAction) {
        actions += act
        removeActionFromMenubar(act)
        removeActionFromToolbar(act)
    }

    private fun removeActionFromToolbar(act: IdeAction) {
        if (act.toolbarId != null) {
            for (it in defaultToolBar.components) {
                if (it is JButton && it.action == act) {
                    defaultToolBar.remove(it)
                    break
                }
            }
        }
    }

    private fun removeActionFromMenubar(act: IdeAction) {
        if (act.menuPath.isNotEmpty()) {
            //TODO
            val a = jMenuBar.getOrCreate(act.menuPath)
        }
    }

    fun getDockable(pred: (CDockable?) -> Boolean): CDockable? {
        for (idx in 0 until globalPort.cDockableCount) {
            val dockable = globalPort.getCDockable(idx)
            if (pred(dockable)) {
                return dockable
            }
        }
        return null
    }

    override fun addEditorTab(editor: CodeEditor) {
        val e = globalPort.focusHistory.history.find { it is CodeEditor }
        lookup.register(editor)
        globalPort.addDockable(editor)
        if (e != null)
            editor.setLocationsAside(e)
        editor.isVisible = true
    }

    fun close() {
        val editor = globalPort.focusedCDockable as? Closeable
        if (editor != null) close(editor)
    }

    fun close(editor: Closeable?) {
        editor?.also {
            it.close()
        }
    }

    fun saveAs(editor: CodeEditor? = currentEditor) =
            editor?.also { it.saveAs() }

    fun save(editor: CodeEditor? = currentEditor) {
        editor?.also { it.save() }
    }

    fun open() {
        val fc = JFileChooser()
        val res = fc.showOpenDialog(this)
        if (res == JFileChooser.APPROVE_OPTION) {
            open(fc.selectedFile)
        }
    }

    override fun open(f: File) {
        if (f !in recentFiles) {
            recentFiles.add(f)
            refreshRecentFiles()
        }
        editorFactory.get(f)?.let(this::addEditorTab)
    }

    override fun addToolTab(window: ToolPane) {
        val otherToolWindow = getDockable { it is ToolPane && it != null }
        globalPort.addDockable(window)
        lookup.register(window)
    }

    override fun jumpTo(editor: CodeEditor, position: Position?) {
        globalPort.controller.setFocusedDockable(
                editor.intern(), editor.textArea, true, true, true
        )
        if (position != null)
            editor.textArea.caretPosition = position.offset
    }

    override fun selectInEditor(name: String, start: Int, stop: Int?) {
        //lookup.getAll<CodeEditor>().forEach {
        globalPort.dockables.filterIsInstance<CodeEditor>().forEach {
            if (it.titleText == name || it.file.toString() == name) {
                jumpTo(it)
                it.textArea.caretPosition = start
                it.textArea.selectionStart = start
                if (stop != null) {
                    it.textArea.selectionEnd = stop
                }
            }
        }
    }

    override fun changeInEditor(editorName: String, start: Int, stop: Int, newText: String) {
        //lookup.getAll<CodeEditor>().forEach {
        globalPort.dockables.filterIsInstance<CodeEditor>().forEach {
            if (it.titleText == editorName || it.file.toString() == editorName) {
                jumpTo(it)
                it.textArea.caretPosition = start
                it.textArea.selectionStart = start
                if (stop != null) {
                    it.textArea.selectionEnd = stop
                }
            }
        }
    }

    fun showFrame() {
        UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName())
        try {
            val xToolkit = Toolkit.getDefaultToolkit()
            val awtAppClassNameField = xToolkit.javaClass.getDeclaredField("awtAppClassName")
            awtAppClassNameField.isAccessible = true
            awtAppClassNameField.set(xToolkit, title)
        } catch (e: Exception) {
            // ignore
            System.err.println(e.message)
        }
        isVisible = true
    }

    fun addActionIntoMenubar(act: Action) = jMenuBar import act

    val actionGotoLine = createAction("Go To Line...", accel = KeyStroke.getKeyStroke("Ctrl-l")) {
        /*if (findDialog.isVisible()) {
            findDialog.setVisible(false)
        }
        if (replaceDialog.isVisible()) {
            replaceDialog.setVisible(false)
        }
         */
        val dialog = GoToDialog(this)
        currentEditor?.textArea?.let { textArea ->
            dialog.maxLineNumberAllowed = textArea.lineCount
            dialog.isVisible = true
            val line = dialog.lineNumber
            if (line > 0) {
                try {
                    textArea.caretPosition = textArea.getLineStartOffset(line - 1)
                } catch (ble: BadLocationException) { // Never happens
                    UIManager.getLookAndFeel().provideErrorFeedback(textArea)
                    ble.printStackTrace()
                }
            }
        }
    }

    private fun refreshRecentFiles() {
        val menu = jMenuBar.getOrCreate("Recent Files")
        menu.removeAll()
        recentFiles.recentFiles
                .map { rf -> createAction(rf.absolutePath) { open(rf) } }
                .forEach { menu.add(it) }
        menu.addSeparator()
        menu.add(actionClearRecentFiles)
    }

    companion object {
        @JvmStatic
        fun main(args: Array<String>) {
            Locale.setDefault(Locale.ENGLISH)

            val rootLookup = Lookup()

            Runtime.getRuntime().addShutdownHook(Thread() {
                val c = rootLookup.get<ConfigurationPaths>().configuration
                rootLookup.get<ApplicationConfiguration>().save(c)
            })


            val configPaths = ConfigurationPaths
            val appConfig = ApplicationConfiguration
            val userConfig = UserConfiguration
            appConfig.properties.load(configPaths.configuration.bufferedReader())

            rootLookup.register(configPaths)
            rootLookup.register(appConfig)
            rootLookup.register(userConfig)
            rootLookup.register<RecentFilesService>(RecentFilesImpl(rootLookup))
            rootLookup.register(Colors)

            val dockableFactory = DockableCodeEditorFactory(rootLookup)
            val editorFactory = EditorFactoryImpl(rootLookup, dockableFactory)
            rootLookup.register<DockableCodeEditorFactory>(dockableFactory)
            rootLookup.register<EditorFactory>(editorFactory)
            FoldParserManager.get().addFoldParserMapping(editorFactory.ttSupport.mimeType, TTFolderParser())
            FoldParserManager.get().addFoldParserMapping(editorFactory.iecSupport.mimeType, STFoldParser())

            UIManager.put("Tree.collapsedIcon", IconFontSwing.buildIcon(FontAwesomeRegular.CARET_SQUARE_RIGHT, 12f))
            UIManager.put("Tree.expandedIcon", IconFontSwing.buildIcon(FontAwesomeSolid.CARET_SQUARE_DOWN, 12f))

            val ide = Ide(rootLookup)
            SwingUtilities.invokeLater {
                ide.showFrame()
                args.forEach {
                    val f = File(it)
                    ide.open(f)
                }
            }
        }
    }
}

class DefaultSearchListener(private val textArea: RSyntaxTextArea? = null,
                            private val lookup: Lookup? = null) : SearchListener {
    override fun searchEvent(e: SearchEvent) {
        val type = e.type
        val context = e.searchContext
        var result: SearchResult? = when (type) {
            SearchEvent.Type.MARK_ALL -> SearchEngine.markAll(textArea, context)
            SearchEvent.Type.FIND -> {
                SearchEngine.find(textArea, context)?.also {
                    if (!it.wasFound()) {
                        UIManager.getLookAndFeel().provideErrorFeedback(textArea)
                    }
                }
            }
            SearchEvent.Type.REPLACE -> {
                SearchEngine.replace(textArea, context)?.also {
                    if (!it.wasFound()) {
                        UIManager.getLookAndFeel().provideErrorFeedback(textArea)
                    }
                }
            }
            SearchEvent.Type.REPLACE_ALL -> {
                SearchEngine.replaceAll(textArea, context)?.also {
                    JOptionPane.showMessageDialog(textArea, it.count.toString() + " occurrences replaced.")
                }
            }
            else -> SearchEngine.markAll(textArea, context)
        }

        val text: String = when {
            result!!.wasFound() -> "Text found; occurrences marked: " + result.markedCount
            type == SearchEvent.Type.MARK_ALL && result.markedCount > 0 ->
                "Occurrences marked: " + result.markedCount
            type == SearchEvent.Type.MARK_ALL -> ""
            else -> "Text not found"
        }
        lookup?.get<StatusService>()?.publishMessage(text)
    }

    override fun getSelectedText(): String? = textArea?.selectedText
}

class EditingDialogsImpl(owner: Frame) : EditingDialogs {
    var lastSearchListener = DefaultSearchListener()
    val findDialog: FindDialog = FindDialog(owner, lastSearchListener)
    val replaceDialog = ReplaceDialog(owner, lastSearchListener)

    init {
        val context = findDialog.searchContext
        replaceDialog.searchContext = context
    }

    override fun openSearchDialog(codeEditor: CodeEditor) {
        findDialog.removeSearchListener(lastSearchListener)
        lastSearchListener = DefaultSearchListener(codeEditor.textArea)
        findDialog.addSearchListener(lastSearchListener)
        replaceDialog.isVisible = false
        findDialog.isVisible = true
    }

    override fun openReplaceDialog(codeEditor: CodeEditor) {
        findDialog.removeSearchListener(lastSearchListener)
        lastSearchListener = DefaultSearchListener(codeEditor.textArea)
        findDialog.addSearchListener(lastSearchListener)
        findDialog.isVisible = false
        replaceDialog.isVisible = true
    }
}


private infix fun JMenuBar.import(it: Action) {
    it.getValue(ACTION_MENU_PATH_KEY)?.also { path ->
        val iter = path.toString().splitToSequence('.').iterator()
        if (!iter.hasNext()) return
        var current = getOrCreate(iter.next())
        iter.forEachRemaining {
            current = this.getOrCreate(it)
        }
        current.add(it)
    }
}

private fun JComponent.getOrCreate(key: String): JMenu {
    this.components.forEach {
        if (it is JMenu && it.text == key) return it
    }
    val m = JMenu(key)
    this.add(m)
    return m
}

private val CControl.dockables: List<CDockable>
    get() = (0 until cDockableCount).map { getCDockable(it) }
