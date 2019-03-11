package edu.kit.iti.formal.automation.ide

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.print.HTMLTablePrinter
import edu.kit.iti.formal.util.CodeWriter
import me.tomassetti.kanvas.*
import me.tomassetti.kolasu.model.Node
import org.antlr.v4.runtime.CharStreams
import org.fife.io.DocumentReader
import org.fife.ui.autocomplete.AutoCompletion
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea
import org.fife.ui.rsyntaxtextarea.RSyntaxUtilities
import org.fife.ui.rsyntaxtextarea.parser.AbstractParser
import org.fife.ui.rsyntaxtextarea.parser.DefaultParseResult
import org.fife.ui.rsyntaxtextarea.parser.DefaultParserNotice
import org.fife.ui.rsyntaxtextarea.parser.ParseResult
import org.fife.ui.rtextarea.RTextScrollPane
import java.awt.BorderLayout
import java.awt.Font
import java.io.File
import java.io.StringWriter
import javax.swing.*
import javax.swing.event.DocumentEvent
import javax.swing.event.DocumentListener
import kotlin.properties.Delegates

/**
 *
 * @author Alexander Weigl
 * @version 1 (11.03.19)
 */
abstract class EditorPane : JPanel(true) {
    abstract val languageSupport: LanguageSupport<*>

    var file: File? by Delegates.observable<File?>(null) { prop, old, new ->
        firePropertyChange(prop.name, old, new)
    }

    var icon: Icon? by Delegates.observable<Icon?>(null) { prop, old, new ->
        firePropertyChange(prop.name, old, new)
    }

    var title: String by Delegates.observable("<UNNAMED>") { prop, old, new ->
        firePropertyChange(prop.name, old, new)
    }

    private fun tabbedPane() = this.parent as JTabbedPane
    private fun index() = tabbedPane().indexOfComponent(this)
    fun close() {
        tabbedPane().removeTabAt(index())
    }

    abstract var textFont: Font

    init {
        addPropertyChangeListener("file") { evt ->
            if (evt.newValue != null)
                title = (evt.newValue as File).name
        }
    }

    abstract fun save()
    abstract fun saveAs()
}

abstract class CodeEditor(lookup: Lookup) : EditorPane() {
    val lookup = Lookup(lookup)
    private val colors: Colors by lookup.with()

    override var languageSupport: LanguageSupport<Node> = noneLanguageSupport
        set(value) {
            (textArea.document as RSyntaxDocument).setSyntaxStyle(AntlrTokenMaker(value.antlrLexerFactory))
            textArea.syntaxScheme = value.syntaxScheme
            field = value
        }

    val textArea = RSyntaxTextArea(20, 60)
    val viewPort = RTextScrollPane(textArea)
    val gutter = RSyntaxUtilities.getGutter(textArea)

    var cachedRoot: Node? = null

    val code: String
        get() = textArea.document.getText(0, textArea.document.length)


    override var textFont: Font
        get() = textArea.font
        set(value) {
            textArea.font = value
            gutter.lineNumberFont = value
        }

    init {
        layout = BorderLayout()
        (textArea.document as RSyntaxDocument).setSyntaxStyle(AntlrTokenMaker(languageSupport.antlrLexerFactory))
        val context = languageSupport.contextCreator.create()
        textArea.syntaxScheme = languageSupport.syntaxScheme
        textArea.isCodeFoldingEnabled = true
        textArea.currentLineHighlightColor = colors.HIGHTLIGHT_LINE
        /*textArea.addParser(object : AbstractParser() {
            override fun parse(doc: RSyntaxDocument, style: String): ParseResult {
                val kolasuParseResult =
                        languageSupport.parser.parse(doc.getText(0, doc.length))
                if (kolasuParseResult.root != null) {
                    cachedRoot = kolasuParseResult.root
                }
                val validator = languageSupport.validator
                val issues = validator.validate(kolasuParseResult, context)
                val kanvasParseResult = DefaultParseResult(this)
                issues.forEach { kanvasParseResult.addNotice(DefaultParserNotice(this, it.message, it.line, it.offset, it.length)) }
                return kanvasParseResult
            }

            override fun isEnabled(): Boolean = true
        })
*/
        val provider = createCompletionProvider(languageSupport, context, { cachedRoot })
        val ac = AutoCompletion(provider)
        ac.install(textArea)
        add(viewPort)
    }

    override fun save() {
        val file = file
        if (file == null) saveAs() else file.writeText(code)
    }


    override fun saveAs() {
        val fc = lookup.get<GetFileChooser>().fileChooser
        val res = fc.showSaveDialog(this)
        if (res == JFileChooser.APPROVE_OPTION) {
            file = fc.selectedFile
            save()
            title = fc.selectedFile.name
            languageSupport = languageSupportRegistry.languageSupportForFile(fc.selectedFile) as LanguageSupport<Node>
        }
    }
}

class STEditor(lookup: Lookup) : CodeEditor(lookup) {
    init {
        languageSupport = IECLanguageSupport(lookup)

        textArea.addParser(object : AbstractParser() {
            val result = DefaultParseResult(this)
            override fun parse(doc: RSyntaxDocument, style: String): ParseResult {
                result.clearNotices()
                val input = DocumentReader(doc)
                val stream = CharStreams.fromReader(input, title)
                val (_, issues) = IEC61131Facade.fileResolve(stream, false)
                issues.forEach {
                    result.addNotice(DefaultParserNotice(this, it.message,
                            it.startLine, it.startOffset, it.length))
                }
                return result
            }

            override fun isEnabled(): Boolean = true
        })

    }
}

class TTEditor(lookup: Lookup) : CodeEditor(lookup) {
    val splitPane = JSplitPane(JSplitPane.HORIZONTAL_SPLIT)
    //var swingbox = org.xhtmlrenderer.simple.XHTMLPanel()
    var swingbox = JEditorPane()
    val viewRender = JScrollPane(swingbox)

    val timer = Timer(500) { e -> render() }

    fun render() {
        try {
            val gtt = GetetaFacade.parseTableDSL(textArea.text)
            val sw = StringWriter()
            val pp = HTMLTablePrinter(gtt, CodeWriter(sw))
            pp.printPreamble()
            pp.print()
            pp.printPostamble()
            print(sw.toString())
            swingbox.text = sw.toString()
            /*swingbox.setDocumentFromString(sw.toString(),
                    File(".").toURI().toString(),
                    XhtmlNamespaceHandler())
                    */
        } catch (e: Exception) {
            e.printStackTrace()
        }
    }

    init {
        swingbox.isEditable = false
        swingbox.contentType = "text/html"

        timer.isRepeats = false
        removeAll()
        splitPane.leftComponent = viewPort
        splitPane.rightComponent = viewRender
        add(splitPane)

        textArea.document.addDocumentListener(object : DocumentListener {
            override fun changedUpdate(e: DocumentEvent?) = update()
            override fun insertUpdate(e: DocumentEvent?) = update()
            override fun removeUpdate(e: DocumentEvent?) = update()
        })
        render()
    }

    fun update() {
        timer.restart()
    }
}
