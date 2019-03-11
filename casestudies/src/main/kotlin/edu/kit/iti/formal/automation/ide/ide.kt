package edu.kit.iti.formal.automation.ide

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import me.tomassetti.kanvas.languageSupportRegistry
import org.fife.ui.rsyntaxtextarea.Style
import org.fife.ui.rsyntaxtextarea.SyntaxScheme
import java.awt.BorderLayout
import java.awt.Color.BLACK
import java.awt.Color.RED
import java.awt.Dimension
import java.awt.Font
import java.awt.Toolkit
import java.awt.event.KeyEvent
import java.io.File
import java.text.ParseException
import javax.swing.*
import kotlin.properties.Delegates

/**
 *
 * @author Alexander Weigl
 * @version 1 (10.03.19)
 */
class Ide(rootLookup: Lookup) : JFrame() {
    private var fontSize: Float by Delegates.observable(12f) { prop, _, new ->
        if (fontSize < 6f) fontSize = 6f
        else {
            defaultFont = defaultFont.deriveFont(new)
            jMenuBar.font = jMenuBar.font.deriveFont(new)
        }
    }

    val lookup = Lookup(rootLookup)

    var defaultFont by Delegates.observable(Font(Font.MONOSPACED, Font.PLAIN, 12)) { _, _, new ->
        (0 until tabbedEditors.tabCount).forEach {
            val c = tabbedEditors.getComponentAt(it) as EditorPane
            c.textFont = new
        }
    }

    val editorFactories = arrayListOf<(File) -> EditorPane?>()
    val tabbedEditors = JTabbedPane()
    val splitPaneRoot = JSplitPane()
    val tabbedTools = JTabbedPane()
    val currentTab: EditorPane?
        get() = tabbedEditors.selectedComponent as EditorPane
    val fileChoser = JFileChooser()
    val defaultToolBar = JToolBar()

    val actions = arrayListOf<MyAction>()

    val actionGeteta = createAction(name = "Geteta", menuPath = "Tools", prio = 10,
            fontIcon = FontAwesomeSolid.TABLE) { runGeteta() }

    val actionReteta = createAction(name = "Reteta", menuPath = "Tools", prio = 10,
            fontIcon = FontAwesomeSolid.TABLET) { runReteta() }

    val actionSaveAs = createAction(name = "Save As", menuPath = "File", prio = 3,
            fontIcon = FontAwesomeSolid.SAVE) { saveAs() }

    val actionRun = createAction(name = "Run", menuPath = "Tools", prio = 9,
            fontIcon = FontAwesomeSolid.RUNNING) { runCurrentProgram() }

    private fun runCurrentProgram() {
        val editor = (currentTab as? STEditor)
        if (editor != null) {
            try {
                val runnerWindow = RunnerWindow(lookup, editor)
                tabbedTools.addTab(runnerWindow.title,
                        actionRun.smallIcon, runnerWindow)
            } catch (e: ParseException) {

            }
        }
    }

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
            fontIcon = FontAwesomeSolid.WINDOW_CLOSE) { close() }

    val actionIncrFontSize = createAction("Increase Font Size", "View",
            KeyStroke.getKeyStroke(KeyEvent.VK_PLUS, KeyEvent.CTRL_DOWN_MASK),
            fontIcon = FontAwesomeSolid.PLUS) { ++fontSize }
    val actionDecrFontSize = createAction("Decrease Font Size", "View",
            KeyStroke.getKeyStroke(KeyEvent.VK_MINUS, KeyEvent.CTRL_DOWN_MASK),
            fontIcon = FontAwesomeSolid.MINUS) { --fontSize }

    val recentFiles by lookup.with<RecentFiles>()

    val actionClearRecentFiles = createAction("Clear recent files",
            "File.Recent Files", prio = 5) {
        recentFiles.clear()
        addRecentFiles()
    }

    init {
        editorFactories.add {
            if (it.name.endsWith("tt.txt")) TTEditor(lookup).also { e ->
                e.file = it
                e.textArea.text = it.readText()
            }
            else null
        }
        editorFactories.add {
            if (it.name.endsWith("st")
                    || it.name.endsWith("iec")
                    || it.name.endsWith("iec61131")) STEditor(lookup).also { e ->
                e.file = it
                e.textArea.text = it.readText()
            }
            else null
        }

        defaultToolBar.add(actionNew)
        defaultToolBar.add(actionOpen)
        defaultToolBar.add(actionSave)
        defaultToolBar.add(actionClose)

        title = "IEC61131 Mini Ide"
        iconImage = IconFontSwing.buildImage(FontAwesomeSolid.PENCIL_RULER, 16f)
        defaultCloseOperation = JFrame.EXIT_ON_CLOSE
        contentPane.layout = BorderLayout(5, 5)
        contentPane.add(defaultToolBar, BorderLayout.NORTH)
        splitPaneRoot.orientation = JSplitPane.VERTICAL_SPLIT
        splitPaneRoot.leftComponent = tabbedEditors
        splitPaneRoot.rightComponent = tabbedTools
        contentPane.add(splitPaneRoot)

        jMenuBar = JMenuBar()

        actions.sortedBy { it.priority }
                .forEach { jMenuBar import it }

        addRecentFiles()
        pack()

        if (width < 500)
            size = Dimension(500, 500)

    }

    fun addTab(editor: EditorPane) {
        tabbedEditors.addTab(editor.title, editor.icon, editor, editor.file?.absolutePath)
    }

    fun createCodeEditor() = addTab(STEditor(lookup))

    fun close(editor: EditorPane? = currentTab) {
        editor?.also {
            it.close()
        }
    }

    fun saveAs(editor: EditorPane? = currentTab) =
            editor?.also { it.saveAs() }

    fun save(editor: EditorPane? = currentTab) {
        editor?.also { it.save() }
    }

    fun open() {
        val fc = JFileChooser()
        val res = fc.showOpenDialog(tabbedEditors)
        if (res == JFileChooser.APPROVE_OPTION) {
            open(fc.selectedFile)
        }
    }

    fun open(f: File) {
        if (f !in recentFiles) {
            recentFiles.add(f)
            addRecentFiles()
        }
        for (it in editorFactories) {
            val p = it(f)
            if (p != null) {
                addTab(p)
                break
            }
        }
    }

    private fun runReteta() {}
    private fun runGeteta() {}

    fun createAndShowKanvasGUI() {
        UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName())
        try {
            val xToolkit = Toolkit.getDefaultToolkit()
            println("XTOOLKIT " + xToolkit)
            val awtAppClassNameField = xToolkit.javaClass.getDeclaredField("awtAppClassName")
            awtAppClassNameField.isAccessible = true
            awtAppClassNameField.set(xToolkit, title)
        } catch (e: Exception) {
            // ignore
            System.err.println(e.message)
        }
        isVisible = true
    }


    private fun addRecentFiles() {
        val m = "File.Recent Files"
        var i = 0
        jMenuBar.getOrCreate("File").getOrCreate("Recent Files").removeAll()
        recentFiles.recentFiles
                .map { rf ->
                    createAction(rf.absolutePath, m, prio = i++, register = false, fontIcon = FontAwesomeSolid.SAVE) {
                        open(rf)
                    }
                }
                .sortedBy { it.priority }
                .forEach { jMenuBar import it }
    }

    private fun createAction(name: String, menuPath: String, accel: KeyStroke? = null,
                             prio: Int = 0,
                             shortDesc: String? = null,
                             longDesc: String? = null,
                             smallIcon: Icon? = null,
                             largeIcon: Icon? = null,
                             register: Boolean = true,
                             fontIcon: FontIcon? = null,
                             f: () -> Unit): MyAction {
        val myAction = LambdaAction(f)
        myAction.priority = prio
        myAction.name = name
        myAction.menuPath = menuPath
        myAction.accelerator = accel
        myAction.shortDescription = shortDesc
        myAction.longDescription = longDesc
        myAction.smallIcon = smallIcon
        myAction.largeIcon = largeIcon

        if (fontIcon != null) {
            myAction.largeIcon = IconFontSwing.buildIcon(fontIcon, 24f)
            myAction.smallIcon = IconFontSwing.buildIcon(fontIcon, 16f)
        }

        if (register)
            actions += myAction
        return myAction
    }

    companion object {
        @JvmStatic
        fun main(args: Array<String>) {
            val rootLookup = Lookup()
            rootLookup.register<RecentFiles>(RecentFilesImpl())
            rootLookup.register(Colors())

            //https://tomassetti.me/kanvas-generating-simple-ide-antlr-grammar/
            val iecSupport = IECLanguageSupport(rootLookup)
            val ttSupport = TestTableLanguageSupport(rootLookup)
            languageSupportRegistry.register("st", iecSupport)
            languageSupportRegistry.register("iec61131", iecSupport)
            languageSupportRegistry.register(".tt", ttSupport)
            languageSupportRegistry.register(".tt.txt", ttSupport)
            languageSupportRegistry.register(".testtable", ttSupport)

            val ide = Ide(rootLookup)
            SwingUtilities.invokeLater {
                ide.createAndShowKanvasGUI()
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


class IEC61131SyntaxScheme(val lookup: Lookup) : SyntaxScheme(true) {
    val colors :Colors by lookup.with()
    val STRUCTURAL_KEYWORDS = setOf(
            IEC61131Lexer.PROGRAM,
            IEC61131Lexer.INITIAL_STEP,
            IEC61131Lexer.TRANSITION,
            IEC61131Lexer.END_TRANSITION,
            IEC61131Lexer.END_VAR,
            IEC61131Lexer.VAR,
            IEC61131Lexer.VAR_ACCESS,
            IEC61131Lexer.VAR_CONFIG,
            IEC61131Lexer.VAR_EXTERNAL,
            IEC61131Lexer.VAR_GLOBAL,
            IEC61131Lexer.VAR_INPUT,
            IEC61131Lexer.VAR_IN_OUT,
            IEC61131Lexer.VAR_OUTPUT,
            IEC61131Lexer.VAR_TEMP,
            IEC61131Lexer.END_PROGRAM,
            IEC61131Lexer.END_ACTION,
            IEC61131Lexer.END_CASE,
            IEC61131Lexer.END_CLASS,
            IEC61131Lexer.END_CONFIGURATION,
            IEC61131Lexer.END_FUNCTION_BLOCK,
            IEC61131Lexer.FUNCTION_BLOCK,
            IEC61131Lexer.FUNCTION,
            IEC61131Lexer.END_FUNCTION,
            IEC61131Lexer.END_INTERFACE,
            IEC61131Lexer.END_METHOD,
            IEC61131Lexer.INTERFACE,
            IEC61131Lexer.METHOD,
            IEC61131Lexer.END_NAMESPACE,
            IEC61131Lexer.NAMESPACE,
            IEC61131Lexer.END_STEP,
            IEC61131Lexer.STEP,
            IEC61131Lexer.ACTION
    )
    val DATATYPE_KEYWORD = setOf(
            IEC61131Lexer.ANY_BIT,
            IEC61131Lexer.ARRAY,
            IEC61131Lexer.STRING,
            IEC61131Lexer.WSTRING,
            IEC61131Lexer.ANY_DATE,
            IEC61131Lexer.ANY_INT,
            IEC61131Lexer.ANY_NUM,
            IEC61131Lexer.ANY_REAL,
            IEC61131Lexer.REAL,
            IEC61131Lexer.LREAL,
            IEC61131Lexer.INT,
            IEC61131Lexer.DINT,
            IEC61131Lexer.UDINT,
            IEC61131Lexer.SINT,
            IEC61131Lexer.USINT,
            IEC61131Lexer.ULINT,
            IEC61131Lexer.DINT,
            IEC61131Lexer.LINT,
            IEC61131Lexer.DATE,
            IEC61131Lexer.DATE_AND_TIME,
            IEC61131Lexer.TIME,
            IEC61131Lexer.WORD,
            IEC61131Lexer.LWORD,
            IEC61131Lexer.DWORD,
            IEC61131Lexer.BOOL
    )
    val LITERALS = setOf(
            IEC61131Lexer.DATE_LITERAL,
            IEC61131Lexer.INTEGER_LITERAL,
            IEC61131Lexer.BITS_LITERAL,
            IEC61131Lexer.CAST_LITERAL,
            IEC61131Lexer.DIRECT_VARIABLE_LITERAL,
            IEC61131Lexer.REAL_LITERAL,
            IEC61131Lexer.STRING_LITERAL,
            IEC61131Lexer.TOD_LITERAL,
            IEC61131Lexer.TIME_LITERAL,
            IEC61131Lexer.WSTRING_LITERAL
    )


    override fun getStyle(index: Int): Style {
        val style = Style()
        val color = when (index) {
            in STRUCTURAL_KEYWORDS -> colors.DARK_VIOLET
            in LITERALS -> colors.VIOLET
            in DATATYPE_KEYWORD -> colors.DARK_GREEN
            IEC61131Lexer.IDENTIFIER -> colors.BLUE
            IEC61131Lexer.COMMENT -> colors.GREY
            IEC61131Lexer.LINE_COMMENT -> colors.GREY
            IEC61131Lexer.ERROR_CHAR -> RED
            else -> BLACK
        }
        if (color != null) {
            style.foreground = color
        }
        return style
    }
}
