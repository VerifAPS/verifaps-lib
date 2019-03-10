package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import me.tomassetti.kanvas.*
import me.tomassetti.kolasu.model.Node
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Lexer
import org.fife.ui.autocomplete.AutoCompletion
import org.fife.ui.autocomplete.BasicCompletion
import org.fife.ui.autocomplete.Completion
import org.fife.ui.autocomplete.CompletionProvider
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea
import org.fife.ui.rsyntaxtextarea.Style
import org.fife.ui.rsyntaxtextarea.SyntaxScheme
import org.fife.ui.rsyntaxtextarea.parser.AbstractParser
import org.fife.ui.rsyntaxtextarea.parser.DefaultParseResult
import org.fife.ui.rsyntaxtextarea.parser.DefaultParserNotice
import org.fife.ui.rsyntaxtextarea.parser.ParseResult
import java.awt.*
import java.awt.Color.*
import java.io.File
import java.util.*
import javax.swing.*
import javax.swing.text.Document
import javax.swing.text.JTextComponent
import kotlin.properties.Delegates


private val BACKGROUND = Color(39, 40, 34)
private val BACKGROUND_SUBTLE_HIGHLIGHT = Color(49, 50, 44)
private val BACKGROUND_DARKER = Color(23, 24, 20)
private val BACKGROUND_LIGHTER = Color(109, 109, 109)


/**
 *
 * @author Alexander Weigl
 * @version 1 (10.03.19)
 */
abstract class EditorPane : JPanel(true) {
    abstract val languageSupport: LanguageSupport<*>

    var file: File? by Delegates.observable<File?>(null) { prop, old, new ->
        firePropertyChange(prop.name, old, new)
    }

    var icon: Icon? by Delegates.observable<Icon?>(null) { prop, old, new ->
        firePropertyChange(prop.name, old, new)
    }

    var title: String
        get() = tabbedPane().getTitleAt(index())
        set(value) {
            val old = title
            tabbedPane().setTitleAt(index(), value)
            firePropertyChange("title", old, value)
        }

    private fun tabbedPane() = this.parent as JTabbedPane
    private fun index() = tabbedPane().indexOfComponent(this)
    fun close() {
        tabbedPane().removeTabAt(index())
    }

    init {
        addPropertyChangeListener("file") { evt ->
            if (evt.newValue != null)
                title = (evt.newValue as File).name
        }
    }

    abstract fun save(ide: Ide)
    abstract fun saveAs(ide: Ide)
}

class CodeEditor() : EditorPane() {
    override val languageSupport by Delegates.observable(iecLanguageSupport) { prop, old, new ->
        (textArea.document as RSyntaxDocument).setSyntaxStyle(AntlrTokenMaker(new.antlrLexerFactory))
        textArea.syntaxScheme = new.syntaxScheme
    }
    val textArea = RSyntaxTextArea(20, 60)

    private var cachedRootField: Node? = null
    var cachedRoot: Node?
        get() = cachedRootField
        set(value) {
            cachedRootField = value
        }

    val text: String
        get() = textArea.text

    val code: String
        get() = textArea.document.getText(0, textArea.document.length)


    var textFont: Font
        get() = textArea.font
        set(value) {
            textArea.font = value
        }

    init {
        layout = BorderLayout()
        (textArea.document as RSyntaxDocument).setSyntaxStyle(AntlrTokenMaker(languageSupport.antlrLexerFactory))
        val context = languageSupport.contextCreator.create()
        textArea.syntaxScheme = languageSupport.syntaxScheme
        textArea.isCodeFoldingEnabled = true
        textArea.currentLineHighlightColor = BACKGROUND_SUBTLE_HIGHLIGHT
        textArea.addParser(object : AbstractParser() {
            override fun parse(doc: RSyntaxDocument, style: String): ParseResult {
                val kolasuParseResult = languageSupport.parser.parse(doc.getText(0, doc.length))
                if (kolasuParseResult.root != null) {
                    cachedRoot = kolasuParseResult.root
                }
                val issues = languageSupport.validator.validate(kolasuParseResult, context)
                val kanvasParseResult = DefaultParseResult(this)
                issues.forEach { kanvasParseResult.addNotice(DefaultParserNotice(this, it.message, it.line, it.offset, it.length)) }
                return kanvasParseResult
            }

            override fun isEnabled(): Boolean = true
        })

        val provider = createCompletionProvider(languageSupport, context, textArea)
        val ac = AutoCompletion(provider)
        ac.install(textArea)

        textPanel.viewportBorder = BorderFactory.createEmptyBorder()
//    try {
//        textPanel.verticalScrollBar.ui = object : SynthScrollBarUI() {
//            override fun configureScrollBarColors() {
//                super.configureScrollBarColors()
//            }
//        }
//    } catch (e: Exception) {
//        System.err.println(e.message)
//    }
        return textPanel
    }
override fun save(ide: Ide) {
    TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
}

override fun saveAs(ide: Ide) {
    TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
}
}


fun createCompletionProvider(languageSupport: LanguageSupport<*>,
                             context: Context,
                             textPanel: RSyntaxTextArea): CompletionProvider {
    if (languageSupport.parserData == null) {
        return object : AbstractCompletionProviderBase() {
            override fun getCompletionsImpl(comp: JTextComponent?): MutableList<Completion> {
                return LinkedList()
            }

        }
    }
    val cp = object : AbstractCompletionProviderBase() {
        val thisACPB = this

        private val autoCompletionSuggester = languageSupport.autoCompletionSuggester()

        private fun pointInCode(comp: JTextComponent) : me.tomassetti.kolasu.model.Point {
            val doc = comp.document
            val dot = comp.caretPosition
            val root = doc.defaultRootElement
            val currLineIndex = root.getElementIndex(dot)
            val currentLine = root.getElement(currLineIndex)
            val startLine = currentLine.startOffset
            return me.tomassetti.kolasu.model.Point(currLineIndex, dot - startLine)
        }

        private fun beforeCaret(comp: JTextComponent) : String {
            val doc = comp.document

            val dot = comp.caretPosition
            val root = doc.defaultRootElement
            val currLineIndex = root.getElementIndex(dot)
            val sb = StringBuffer()
            for (i in 0 until currLineIndex) {
                val elem = root.getElement(i)
                var start = elem.startOffset
                val len = elem.endOffset - start
                sb.append(doc.getText(start, len))
            }

            sb.append(beforeCaretOnCurrentLine(doc, dot, currLineIndex))
            return sb.toString()
        }

        private fun beforeCaretOnCurrentLine(doc: Document, dot:Int, currLineIndex: Int) : String {
            val root = doc.defaultRootElement
            val elem = root.getElement(currLineIndex)
            var start = elem.startOffset
            val len = dot - start
            return doc.getText(start, len)
        }

        override fun getCompletionsImpl(comp: JTextComponent): MutableList<Completion>? {
            val retVal = ArrayList<Completion>()
            val code = beforeCaret(comp)
            val autoCompletionContext = autoCompletionSuggester.autoCompletionContext(
                    EditorContextImpl(code, languageSupport.antlrLexerFactory, textPanel))
            autoCompletionContext.proposals.forEach {
                if (it.first.type != -1) {
                    retVal.addAll(languageSupport.propositionProvider.fromTokenType(
                            AutocompletionSurroundingInformation(
                                    textPanel.cachedRoot,
                                    autoCompletionContext.preecedingTokens,
                                    it.second,
                                    pointInCode(comp)), it.first.type, context).map {
                        BasicCompletion(thisACPB, it)
                    })
                }
            }

            return retVal

        }

    }
    return cp
}


class Ide {
    val appTitle = "IEC61131 Mini Ide"

    var defaultFont by Delegates.observable(Font(Font.MONOSPACED, Font.PLAIN, 12),
            onChange = { prop, old, new ->
                tabbedPane.getTabComponentAt(0).font = new
            })

    val editorFactories = arrayListOf<(File) -> EditorPane?>()

    val tabbedPane = JTabbedPane()

    fun addTab(editor: EditorPane) {
        tabbedPane.addTab(editor.title, editor.icon, editor, editor.file?.absolutePath)
    }

    val currentTab: EditorPane?
        get() = tabbedPane.selectedComponent as EditorPane

    private fun createCodeEditor(): Unit {

    }

    private fun openCommand() {
        val fc = JFileChooser()
        val res = fc.showOpenDialog(tabbedPane)
        if (res == JFileChooser.APPROVE_OPTION) {
            openFile(fc.selectedFile)
        }
    }

    private fun openFile(f: File) {
        for (it in editorFactories) {
            val p = it(f)
            if (p != null) {
                addTab(p)
                break
            }
        }
    }

    private fun createKanvasIcon(): Image {
        val url = ClassLoader.getSystemResource("kanvas-logo.png")
        val kit = Toolkit.getDefaultToolkit()
        val img = kit.createImage(url)
        return img
    }

    protected fun populateMenu(menuBar: JMenuBar) {
        val fileMenu = JMenu("File")
        menuBar.add(fileMenu)
        val open = JMenuItem("Open")
        open.addActionListener { openCommand() }
        fileMenu.add(open)
        val new = JMenuItem("New")
        new.addActionListener { addTab("<UNNAMED>") }
        fileMenu.add(new)
        val save = JMenuItem("Save")
        save.addActionListener { saveCommand(tabbedPane) }
        fileMenu.add(save)
        val saveAs = JMenuItem("Save as")
        saveAs.addActionListener { saveAsCommand(tabbedPane) }
        fileMenu.add(saveAs)
        val close = JMenuItem("Close")
        close.addActionListener { closeCommand(tabbedPane) }
        fileMenu.add(close)
    }

    fun createAndShowKanvasGUI() {
        //UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName())
        try {
            val xToolkit = Toolkit.getDefaultToolkit()
            println("XTOOLKIT " + xToolkit)
            val awtAppClassNameField = xToolkit.javaClass.getDeclaredField("awtAppClassName")
            awtAppClassNameField.isAccessible = true
            awtAppClassNameField.set(xToolkit, appTitle)
        } catch (e: Exception) {
            // ignore
            System.err.println(e.message)
        }

        val frame = JFrame(appTitle)
        frame.iconImage = createKanvasIcon()
        frame.defaultCloseOperation = JFrame.EXIT_ON_CLOSE

        frame.contentPane.add(tabbedPane)

        val menuBar = JMenuBar()
        populateMenu(menuBar)
        frame.jMenuBar = menuBar

        frame.pack()
        if (frame.width < 500) {
            frame.size = Dimension(500, 500)
        }
        frame.isVisible = true
    }

    companion object {
        @JvmStatic
        fun main(args: Array<String>) {
            //https://tomassetti.me/kanvas-generating-simple-ide-antlr-grammar/
            languageSupportRegistry.register("st", iecLanguageSupport)
            languageSupportRegistry.register("iec61131", iecLanguageSupport)

            val ide = Ide()

            SwingUtilities.invokeLater {
                ide.createAndShowKanvasGUI()
                UIManager.setLookAndFeel(com.alee.laf.WebLookAndFeel())
                args.forEach { it ->
                    val f = File(it)
                    ide.openFile(f)
                }
            }
        }
    }
}

val STRUCTURAL_KEYWORDS = setOf(
        IEC61131Lexer.PROGRAM,
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

object iec61131SyntaxScheme : SyntaxScheme(true) {
    override fun getStyle(index: Int): Style {
        val style = Style()
        val color = when (index) {
            in STRUCTURAL_KEYWORDS -> BLUE
            in LITERALS -> GREEN
            in DATATYPE_KEYWORD -> ORANGE
            IEC61131Lexer.COMMENT -> LIGHT_GRAY
            IEC61131Lexer.LINE_COMMENT -> LIGHT_GRAY
            IEC61131Lexer.ERROR_CHAR -> RED
            else -> WHITE
        }
        if (color != null) {
            style.foreground = color
        }
        return style
    }
}

/*
object IEC61131Parser : me.tomassetti.kolasu.parsing.Parser<Node> {
    override fun parse(inputStream: InputStream, withValidation: Boolean): ParsingResult<Node> {
        return
    }
}
*/

object iecLanguageSupport : BaseLanguageSupport<me.tomassetti.kolasu.model.Node>() {
    override val parser: me.tomassetti.kolasu.parsing.Parser<Node>
        get() = TODO()
    override val syntaxScheme: SyntaxScheme
        get() = iec61131SyntaxScheme
    override val antlrLexerFactory: AntlrLexerFactory
        get() = object : AntlrLexerFactory {
            override fun create(code: String): Lexer =
                    IEC61131Lexer(CharStreams.fromString(code))
        }
    override val parserData: ParserData?
        get() = ParserData(IEC61131Parser.ruleNames, IEC61131Parser.VOCABULARY, IEC61131Parser._ATN)
}