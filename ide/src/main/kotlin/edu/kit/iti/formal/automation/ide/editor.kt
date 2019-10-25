package edu.kit.iti.formal.automation.ide

import bibliothek.gui.dock.common.DefaultMultipleCDockable
import bibliothek.gui.dock.common.MultipleCDockableFactory
import bibliothek.gui.dock.common.MultipleCDockableLayout
import bibliothek.util.xml.XElement
import edu.kit.iti.formal.automation.ide.editors.IECLanguageSupport
import edu.kit.iti.formal.automation.ide.editors.SmvLanguageSupport
import edu.kit.iti.formal.automation.ide.editors.TestTableLanguageSupport
import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import me.tomassetti.kanvas.AntlrTokenMakerFactory
import me.tomassetti.kanvas.LanguageSupport
import me.tomassetti.kanvas.NoneLanguageSupport
import org.fife.rsta.ui.CollapsibleSectionPanel
import org.fife.rsta.ui.search.FindToolBar
import org.fife.rsta.ui.search.ReplaceToolBar
import org.fife.ui.autocomplete.AbstractCompletionProvider
import org.fife.ui.autocomplete.AutoCompletion
import org.fife.ui.autocomplete.Completion
import org.fife.ui.autocomplete.DefaultCompletionProvider
import org.fife.ui.rsyntaxtextarea.ErrorStrip
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea
import org.fife.ui.rsyntaxtextarea.RSyntaxUtilities
import org.fife.ui.rtextarea.Gutter
import org.fife.ui.rtextarea.RTextScrollPane
import java.awt.BorderLayout
import java.awt.Font
import java.awt.event.KeyEvent
import java.io.DataInputStream
import java.io.DataOutputStream
import java.io.File
import javax.swing.Action
import javax.swing.JComponent
import javax.swing.JFileChooser
import javax.swing.KeyStroke
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

data class CodeEditorData(var file: File?) : MultipleCDockableLayout {
    override fun writeStream(p0: DataOutputStream) {
        (file?.absolutePath ?: "").let {
            p0.writeUTF(it)
        }
    }

    override fun readXML(p0: XElement) {
        file = File(p0.getAttribute("file").value)
        //type = p0.getAttribute("type").value
    }

    override fun writeXML(p0: XElement) {
        p0.getAttribute("file").value = file?.absolutePath
        //p0.getAttribute("type").value = type
    }

    override fun readStream(p0: DataInputStream) {
        file = File(p0.readUTF())
        //type = p0.readUTF()
    }
}

interface EditorFactory {
    fun get(file: File): CodeEditor?
    fun getLanguage(it: File): LanguageSupport?
    fun getSupportedSuffixes(): Collection<String>
}

class EditorFactoryImpl(val lookup: Lookup,
                        private val factory: MultipleCDockableFactory<*, *>)
    : EditorFactory {

    override fun getSupportedSuffixes(): Collection<String> {
        return (ttSupport.extension
                + iecSupport.extension
                + smvSupport.extension
                + NoneLanguageSupport.extension + listOf("xml")).toSet()
    }

    val ttSupport = TestTableLanguageSupport(lookup)
    val iecSupport = IECLanguageSupport(lookup)
    val smvSupport = SmvLanguageSupport(lookup)

    val languageSupports = mutableListOf(
            ttSupport, smvSupport, iecSupport)

    val editorFactories = arrayListOf<(File) -> CodeEditor?>()

    override fun getLanguage(it: File): LanguageSupport? {
        for (language in languageSupports) {
            if (it.extension in language.extension) {
                return language
            }
        }
        return null
    }

    fun default(file: File): CodeEditor? {
        return getLanguage(file)?.let { createCodeEditor(file, it) }
    }

    fun createCodeEditor(it: File, language: LanguageSupport): CodeEditor {
        val codeEditor = CodeEditor(lookup, factory)
        codeEditor.languageSupport = language
        codeEditor.file = it
        codeEditor.textArea.text = try {
            it.readText()
        } catch (e: Exception) {
            ""
        }
        codeEditor.dirty = false
        return codeEditor
    }

    init {
        editorFactories.add(this::default)
        editorFactories.add(this::pclOpenXml)
        editorFactories.add(this::fallback)
    }

    fun fallback(it: File): CodeEditor = createCodeEditor(it, NoneLanguageSupport)

    fun pclOpenXml(it: File): CodeEditor? {
        return if (it.name.endsWith("xml")) {
            val stCode = IECXMLFacade.extractPLCOpenXml(it)
            val f = File(it.parentFile, it.nameWithoutExtension + ".st")
            f.writeText(stCode)
            createCodeEditor(f, IECLanguageSupport(lookup))
        } else null
    }

    override fun get(file: File): CodeEditor? {
        for (it in editorFactories) {
            val p = it(file)
            if (p != null) {
                return p
            }
        }
        return null
    }
}

class DockableCodeEditorFactory(var lookup: Lookup)
    : MultipleCDockableFactory<CodeEditor, CodeEditorData> {
    override fun write(p0: CodeEditor): CodeEditorData = CodeEditorData(p0.file)

    override fun create(): CodeEditorData = CodeEditorData(File("empty"))

    override fun read(p0: CodeEditorData): CodeEditor? {
        return p0.file?.let {
            lookup.get<EditorFactory>().get(it)
        }
    }

    override fun match(p0: CodeEditor?, p1: CodeEditorData?): Boolean = p0?.file == p1?.file
}

class CodeEditor(val lookup: Lookup, factory: MultipleCDockableFactory<*, *>)
    : DefaultMultipleCDockable(factory), Saveable, HasFont, Closeable {
    private val colors: Colors by lookup.with()
    var text: String
        get() = textArea.text
        set(value) {
            textArea.text = value
        }

    var languageSupport by Delegates.observable<LanguageSupport>(NoneLanguageSupport) { prop, old, new ->
        if (old != new) {
            textArea.clearParsers()
            textArea.syntaxEditingStyle = new.mimeType
            (textArea.document as RSyntaxDocument).setSyntaxStyle(AntlrTokenMakerFactory(new.antlrLexerFactory))
            textArea.syntaxScheme = new.syntaxScheme
            textArea.addParser(new.createParser(this, lookup))
            textArea.isCodeFoldingEnabled = new.isCodeFoldingEnabled
        }
    }

    val textArea = RSyntaxTextArea(20, 60)

    val viewPort = RTextScrollPane(textArea)

    val gutter: Gutter = RSyntaxUtilities.getGutter(textArea)

    val code: String
        get() = textArea.document.getText(0, textArea.document.length)


    var file: File? by Delegates.observable<File?>(null) { prop, old, new ->
        titleText = title
    }

    var dirty: Boolean by Delegates.observable(false) { prop, old, new ->
        titleText = title
    }

    private val DIRTY_MARKER = '*'
    private val title: String
        get() = (file?.name ?: "EMPTY") + (if (dirty) DIRTY_MARKER else "")

    override var textFont: Font
        get() = textArea.font
        set(value) {
            textArea.font = value
            gutter.lineNumberFont = value
        }

    val rootPanel = CollapsibleSectionPanel()
    val errorStrip = ErrorStrip(textArea)

    val searchListener = DefaultSearchListener(textArea)
    val findToolBar = FindToolBar(searchListener)
    val replaceToolBar = ReplaceToolBar(searchListener)

    val actionShowFindToolBar = rootPanel.addBottomComponent(KeyStroke.getKeyStroke(KeyEvent.VK_F, KeyEvent.CTRL_DOWN_MASK), findToolBar)
    val actionShowReplaceToolBar = rootPanel.addBottomComponent(KeyStroke.getKeyStroke("ctrl R"), replaceToolBar)

    init {
        textFont = lookup.get<Colors>().defaultFont
        contentPane.layout = BorderLayout()
        (textArea.document as RSyntaxDocument).setSyntaxStyle(AntlrTokenMakerFactory(languageSupport.antlrLexerFactory))
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
        //val provider = createCompletionProvider(languageSupport, context, { cachedRoot })
        /*val provider = object : DefaultCompletionProvider() {
            override fun getCompletionByInputText(inputText: String?): MutableList<Completion> {
                println(inputText)
                return super.getCompletionByInputText(inputText)
            }
        }
        val ac = AutoCompletion(provider)
        ac.install(textArea)*/
        contentPane.layout = BorderLayout()
        titleText = "EMPTY"
        isCloseable = true

        rootPanel.add(viewPort)
        contentPane.add(errorStrip, BorderLayout.LINE_END)
        contentPane.add(rootPanel)

        actionShowFindToolBar.activateKeystroke(contentPane as JComponent)
        actionShowReplaceToolBar.activateKeystroke(contentPane as JComponent)

        //org.fife.rsta.ui.DocumentMap docMap = new org.fife.rsta.ui.DocumentMap(textArea);
        //contentPane.add(docMap, BorderLayout.LINE_END);
    }


    override fun close() {
        //DockingManager.undock(dockable)
    }

    override fun save() {
        val file = file
        if (file == null) saveAs() else file.writeText(code)
        file?.also {
            lookup.get<EditorFactory>().getLanguage(it)?.also {
                languageSupport = it
            }
        }
        dirty = false
    }

    override fun saveAs() {
        val fc = lookup.get<GetFileChooser>().fileChooser
        val res = fc.showSaveDialog(contentPane)
        if (res == JFileChooser.APPROVE_OPTION) {
            file = fc.selectedFile
            save()
        }
    }
}

fun Action.activateKeystroke(comp: JComponent) {
    (getValue(Action.ACCELERATOR_KEY) as? KeyStroke)?.also { activateKeystroke(comp, it) }
}

fun Action.activateKeystroke(comp: JComponent, ks: KeyStroke) {
    comp.registerKeyboardAction(this, ks,
            JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT or JComponent.WHEN_FOCUSED)
}
