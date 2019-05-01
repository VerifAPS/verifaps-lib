package edu.kit.iti.formal.automation.ide

import bibliothek.gui.dock.common.DefaultMultipleCDockable
import bibliothek.gui.dock.common.NullMultipleCDockableFactory
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.parser.ErrorReporter
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
import org.fife.ui.rtextarea.Gutter
import org.fife.ui.rtextarea.RTextScrollPane
import java.awt.BorderLayout
import java.awt.Font
import java.io.File
import java.lang.Exception
import javax.swing.JFileChooser
import javax.swing.Timer
import javax.swing.event.DocumentEvent
import javax.swing.event.DocumentListener
import kotlin.properties.Delegates


interface Saveable {
    fun saveAs()
    fun save()
}

interface Closeable {
    fun close()
}

interface HasFont {
    var textFont: Font
}

/*abstract class TabbedPanel() : JPanel(true), Closeable {
    constructor(l: LayoutManager) : this() {
        layout = l
        title = "UNKNOWN"
    }

    open val dockable: CDockable? by lazy {
        DefaultSingleCDockable(javaClass.toString(), icon, title, this)
                .also {
                    it.setLocation(CLocation.base().normalSouth(.2))
                }
    }

    var title: String? = null
        set(value) {
            firePropertyChange("title", field, value)
            field = value
        }

    var icon: Icon? = null
        set(value) {
            firePropertyChange("icon", field, value)
            field = value
        }

    var tip: String? = null
        set(value) {
            firePropertyChange("tip", field, value)
            field = value
        }


    fun getComponent(): Component = this
}*/

val dockableFactory = NullMultipleCDockableFactory.NULL

abstract class CodeEditor(lookup: Lookup) : DefaultMultipleCDockable(dockableFactory), Saveable, HasFont, Closeable {
    val lookup = Lookup(lookup)
    private val DIRTY_MARKER = '*'
    private val colors: Colors by lookup.with()
    var text: String
        get() = textArea.text
        set(value) {
            textArea.text = value
        }

    var languageSupport: LanguageSupport<Node> = noneLanguageSupport
        set(value) {
            (textArea.document as RSyntaxDocument).setSyntaxStyle(AntlrTokenMaker(value.antlrLexerFactory))
            textArea.syntaxScheme = value.syntaxScheme
            field = value
        }

    val textArea = RSyntaxTextArea(20, 60)

    val viewPort = RTextScrollPane(textArea)

    val gutter: Gutter = RSyntaxUtilities.getGutter(textArea)

    var cachedRoot: Node? = null

    val code: String
        get() = textArea.document.getText(0, textArea.document.length)

    var dirty = false
        set(value) {
            field = value
            titleText = if (!value)
                titleText.trim(DIRTY_MARKER)
            else
                titleText.trim(DIRTY_MARKER) + DIRTY_MARKER
        }

    override var textFont: Font
        get() = textArea.font
        set(value) {
            textArea.font = value
            gutter.lineNumberFont = value
        }

    var file: File? by Delegates.observable<File?>(null) { prop, old, new ->
        titleText = (new?.name ?: "EMPTY") + (if (dirty) "*" else "")
    }

    init {
        contentPane.layout = BorderLayout()
        (textArea.document as RSyntaxDocument).setSyntaxStyle(AntlrTokenMaker(languageSupport.antlrLexerFactory))
        val context = languageSupport.contextCreator.create()
        textArea.syntaxScheme = languageSupport.syntaxScheme
        textArea.isCodeFoldingEnabled = true
        textArea.currentLineHighlightColor = colors.HIGHTLIGHT_LINE
        textArea.background = colors.background

        textArea.document.addDocumentListener(object : DocumentListener {
            override fun changedUpdate(e: DocumentEvent?) {
                dirty = true
            }

            override fun insertUpdate(e: DocumentEvent?) {
                dirty = true
            }

            override fun removeUpdate(e: DocumentEvent?) {
                dirty = true
            }
        })


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
        contentPane.layout = BorderLayout()
        titleText = "EMPTY"
        isCloseable = true
        add(viewPort)
    }


    override fun close() {
        //DockingManager.undock(dockable)
    }

    override fun save() {
        val file = file
        if (file == null) saveAs() else file.writeText(code)
    }

    override fun saveAs() {
        val fc = lookup.get<GetFileChooser>().fileChooser
        val res = fc.showSaveDialog(contentPane)
        if (res == JFileChooser.APPROVE_OPTION) {
            file = fc.selectedFile
            save()
            //titleText = fc.selectedFile.name
            languageSupport = languageSupportRegistry.languageSupportForFile(fc.selectedFile) as LanguageSupport<Node>
        }
    }
}

class UnknownTextEditor(lookup: Lookup) : CodeEditor(lookup) {
    init {
        languageSupport = noneLanguageSupport
    }
}

class STEditor(lookup: Lookup) : CodeEditor(lookup) {
    val problemList by super.lookup.with<ProblemList>()

    val editorId = "" + Math.random()

    init {
        textArea.syntaxEditingStyle = "text/st"
        languageSupport = IECLanguageSupport(lookup)
        textArea.isCodeFoldingEnabled = true

        textArea.addParser(object : AbstractParser() {
            val result = DefaultParseResult(this)
            override fun parse(doc: RSyntaxDocument, style: String): ParseResult {
                result.clearNotices()
                val input = DocumentReader(doc)
                val stream = CharStreams.fromReader(input, titleText)
                try {
                    val (_, issues) = IEC61131Facade.fileResolve(stream, false)
                    issues.forEach {
                        result.addNotice(DefaultParserNotice(this, it.message,
                                it.startLine, it.startOffset, it.length))
                    }
                    problemList.set(editorId, issues)
                } catch (e: ErrorReporter.IEC61131ParserException) {
                    e.errors.forEach {
                        result.addNotice(DefaultParserNotice(this, it.msg,
                                it.line, it.offendingSymbol?.startIndex ?: -1,
                                it.offendingSymbol?.text?.length ?: -1))
                    }
                } catch (e: Exception) {
                }
                return result

            }

            override fun isEnabled(): Boolean = true
        })
    }
}

class TTEditor(lookup: Lookup) : CodeEditor(lookup) {
    val timer = Timer(500) { _ -> EVENT_BUS.post(EventGetetaUpdate(textArea.text)) }

    init {
        languageSupport = TestTableLanguageSupport(lookup)

        textArea.document.addDocumentListener(object : DocumentListener {
            override fun changedUpdate(e: DocumentEvent?) = update()
            override fun insertUpdate(e: DocumentEvent?) = update()
            override fun removeUpdate(e: DocumentEvent?) = update()
        })
        timer.isRepeats = false
        //render()
    }

    fun update() {
        timer.restart()
    }
}
