package edu.kit.iti.formal.automation.ide

import bibliothek.gui.dock.common.CControl
import bibliothek.gui.dock.common.CGrid
import bibliothek.gui.dock.common.intern.CDockable
import bibliothek.gui.dock.util.Priority
import edu.kit.iti.formal.automation.ide.tools.GetetaPreview
import me.tomassetti.kanvas.languageSupportRegistry
import org.fife.ui.rsyntaxtextarea.folding.CurlyFoldParser
import org.fife.ui.rsyntaxtextarea.folding.FoldParser
import org.fife.ui.rsyntaxtextarea.folding.FoldParserManager
import java.awt.*
import java.awt.event.KeyEvent
import java.io.File
import java.text.ParseException
import javax.swing.*
import kotlin.properties.Delegates

class EditorFactory(val lookup: Lookup) {
    val editorFactories = arrayListOf<(File) -> CodeEditor?>()

    init {
        editorFactories.add {
            if (it.name.endsWith("gtt")) TTEditor(lookup).also { e ->
                e.file = it
                e.textArea.text = it.readText()
                e.dirty = false
            }
            else null
        }

        editorFactories.add {
            if (it.name.endsWith("st")
                    || it.name.endsWith("iec")
                    || it.name.endsWith("iec61131")) STEditor(lookup).also { e ->
                e.file = it
                e.textArea.text = it.readText()
                e.dirty = false
            }
            else null
        }

        editorFactories.add {
            UnknownTextEditor(lookup).also { e ->
                e.file = it
                e.textArea.text = it.readText()
                e.dirty = false
            }
        }
    }

    fun get(file: File): CodeEditor? {
        for (it in editorFactories) {
            val p = it(file)
            if (p != null) {
                return p
            }
        }
        return null
    }
}

/**
 *
 * @author Alexander Weigl
 * @version 1 (10.03.19)
 */
class Ide(rootLookup: Lookup, vararg initialFiles: File) : JFrame(),
        GetFileChooser, FileOpen,
        TabManagement, ActionService {

    private var fontSize: Float by Delegates.observable(12f) { prop, _, new ->
        if (fontSize < 6f) fontSize = 6f
        else {
            defaultFont = defaultFont.deriveFont(new)
            jMenuBar.font = jMenuBar.font.deriveFont(new)
        }
    }

    val lookup = Lookup(rootLookup)

    var defaultFont by Delegates.observable(Font(Font.MONOSPACED, Font.PLAIN, 12)) { _, _, new ->
        lookup.getAll<CodeEditor>().forEach {
            it.textFont = new
        }
    }

    val allEditors: List<CodeEditor>
        get() {
            return lookup.getAll()
        }

    val currentEditor: CodeEditor?
        get() = currentTabbedPanel as? CodeEditor

    val currentTabbedPanel: CDockable?
        get() = globalPort.controller.focusedDockable as? CDockable

    override val fileChooser = JFileChooser()
    val defaultToolBar = JToolBar()

    val actions = arrayListOf<IdeAction>()

    val actionSaveAs = createAction(name = "Save As", menuPath = "File", prio = 3,
            fontIcon = FontAwesomeSolid.SAVE) { saveAs() }
    val actionRun = createAction(name = "Run", menuPath = "Tools", prio = 9,
            fontIcon = FontAwesomeSolid.RUNNING) { runCurrentProgram() }
    val actionSave = createAction("Save", "File",
            KeyStroke.getKeyStroke(KeyEvent.VK_S, KeyEvent.CTRL_DOWN_MASK), 2,
            fontIcon = FontAwesomeRegular.SAVE) { save() }
    val actionNew = createAction("New", "File",
            KeyStroke.getKeyStroke(KeyEvent.VK_N, KeyEvent.CTRL_DOWN_MASK), 0,
            fontIcon = FontAwesomeRegular.FILE) { createCodeEditor() }
    val actionOpen = createAction("Open", "File",
            KeyStroke.getKeyStroke(KeyEvent.VK_O, KeyEvent.CTRL_DOWN_MASK), 1,
            fontIcon = FontAwesomeRegular.FOLDER_OPEN) { open() }
    val actionClose = createAction("Close", "File",
            KeyStroke.getKeyStroke(KeyEvent.VK_Q, KeyEvent.CTRL_DOWN_MASK), 4,
            fontIcon = FontAwesomeSolid.WINDOW_CLOSE) { /*close()*/ }
    val actionIncrFontSize = createAction("Increase Font Size", "View",
            KeyStroke.getKeyStroke(KeyEvent.VK_PLUS, KeyEvent.CTRL_DOWN_MASK),
            fontIcon = FontAwesomeSolid.PLUS) { ++fontSize }
    val actionDecrFontSize = createAction("Decrease Font Size", "View",
            KeyStroke.getKeyStroke(KeyEvent.VK_MINUS, KeyEvent.CTRL_DOWN_MASK),
            fontIcon = FontAwesomeSolid.MINUS) { --fontSize }

    val editorFactory = EditorFactory(lookup)

    val recentFiles by lookup.with<RecentFilesService>()

    val actionClearRecentFiles = createAction("Clear recent files",
            "File.Recent Files", prio = 5) {
        recentFiles.clear()
        addRecentFiles()
    }

    private fun runCurrentProgram() {
        val editor = (null as? STEditor)
        if (editor != null) {
            try {
                val runnerWindow = RunnerWindow(lookup, editor)
                addToolTab(runnerWindow)
            } catch (e: ParseException) {

            }
        }
    }

    var globalPort = CControl()

    init {
        lookup.register<GetFileChooser>(this)
        lookup.register<FileOpen>(this)
        lookup.register<ProblemList>(ProblemList())

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

        defaultToolBar.add(actionNew)
        defaultToolBar.add(actionOpen)
        defaultToolBar.add(actionSave)
        defaultToolBar.add(actionClose)

        title = "IEC61131 Mini Ide"
        iconImage = IconFontSwing.buildImage(FontAwesomeSolid.PENCIL_RULER, 16f)
        defaultCloseOperation = EXIT_ON_CLOSE
        contentPane.layout = BorderLayout(5, 5)
        contentPane.add(defaultToolBar, BorderLayout.NORTH)
        contentPane.add(globalPort.contentArea, BorderLayout.CENTER)

        jMenuBar = JMenuBar()
        actions.sortedBy { it.priority }
                .forEach { jMenuBar import it }
        addRecentFiles()

        val tree = FileTreePanel(lookup)
        val grid = CGrid(globalPort)
        grid.add(0.0, 0.0, 0.1, 0.5, tree)

        if (initialFiles.isEmpty()) {
            val editor = STEditor(lookup)
            grid.add(1.0, 0.0, 5.0, 4.0, editor)
        } else {
            val docks = initialFiles.mapNotNull(editorFactory::get)
            docks.forEach(lookup::register)
            grid.add(1.0, 0.0, 5.0, 4.0,
                    *(docks.map { it }.toTypedArray()))
        }
        val tools = listOf(
                GetetaPreview(lookup),
                GetetaWindow(lookup),
                RetetaWindow(lookup),
                ProblemPanel(lookup))

        grid.add(1.0, 4.0, 5.0, 1.0, *(tools.toTypedArray()))

        globalPort.contentArea.deploy(grid)


        size = Dimension(700, 800)

        invalidate()
        revalidate()
        revalidate()
        repaint()
        repaint()
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

        /*return when {
            pred(globalPort.cDockableCount) -> globalPort.selectedDockable
            else -> globalPort.dockables.findLast { pred(it.dockable) && it.isDocked }?.dockable
        }
         */
        return null
    }

    override fun addEditorTab(editor: CodeEditor) {
        val e = globalPort.getCDockable(1)
        lookup.register(editor)
        globalPort.addDockable(editor)
        editor.setLocationsAside(e)
        editor.isVisible = true
        //globalPort.createTab(editorPane, editor, 0, true)
    }

    fun createCodeEditor() = addEditorTab(STEditor(lookup))

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
            addRecentFiles()
        }
        editorFactory.get(f)?.let(this::addEditorTab)
    }

    override fun addToolTab(window: ToolPane) {
        val otherToolWindow = getDockable { it is ToolPane && it != null }
        globalPort.addDockable(window)
        lookup.register(window)
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

    private fun addRecentFiles() {
        val m = "File.Recent Files"
        var i = 0
        jMenuBar.getOrCreate("File").getOrCreate("Recent Files").removeAll()
        recentFiles.recentFiles
                .map { rf ->
                    createAction(rf.absolutePath, m, prio = i++, fontIcon = FontAwesomeSolid.SAVE) {
                        open(rf)
                    }
                }
                .sortedBy { it.priority }
                .forEach { jMenuBar import it }
    }

    companion object {
        @JvmStatic
        fun main(args: Array<String>) {
            val rootLookup = Lookup()
            rootLookup.register<RecentFilesService>(RecentFilesImpl())
            rootLookup.register(Colors)

            //https://tomassetti.me/kanvas-generating-simple-ide-antlr-grammar/
            val iecSupport = IECLanguageSupport(rootLookup)
            val ttSupport = TestTableLanguageSupport(rootLookup)
            languageSupportRegistry.register("st", iecSupport)
            languageSupportRegistry.register("iec61131", iecSupport)
            languageSupportRegistry.register(".gtt", ttSupport)
            languageSupportRegistry.register(".tt", ttSupport)
            languageSupportRegistry.register(".tt.txtFolder", ttSupport)
            languageSupportRegistry.register(".testtable", ttSupport)

            FoldParserManager.get().addFoldParserMapping("text/test-table", CurlyFoldParser())
            FoldParserManager.get().addFoldParserMapping("text/st", STFoldParser())


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

