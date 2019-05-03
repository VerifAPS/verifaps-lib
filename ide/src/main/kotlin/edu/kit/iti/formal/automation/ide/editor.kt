package edu.kit.iti.formal.automation.ide

import bibliothek.gui.dock.common.DefaultMultipleCDockable
import bibliothek.gui.dock.common.NullMultipleCDockableFactory
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.ide.tools.OverviewStructureNode
import edu.kit.iti.formal.automation.ide.tools.ShowOverview
import edu.kit.iti.formal.automation.ide.tools.StructureData
import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import me.tomassetti.kanvas.*
import me.tomassetti.kolasu.model.Node
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.ParserRuleContext
import org.fife.io.DocumentReader
import org.fife.rsta.ui.CollapsibleSectionPanel
import org.fife.rsta.ui.search.FindToolBar
import org.fife.rsta.ui.search.ReplaceToolBar
import org.fife.ui.autocomplete.AutoCompletion
import org.fife.ui.rsyntaxtextarea.ErrorStrip
import org.fife.ui.rsyntaxtextarea.RSyntaxDocument
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea
import org.fife.ui.rsyntaxtextarea.RSyntaxUtilities
import org.fife.ui.rsyntaxtextarea.parser.*
import org.fife.ui.rtextarea.Gutter
import org.fife.ui.rtextarea.RTextScrollPane
import java.awt.*
import java.awt.event.KeyEvent
import java.awt.image.BufferedImage
import java.io.File
import java.lang.Exception
import javax.swing.*
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

    val rootPanel = CollapsibleSectionPanel()
    val errorStrip = ErrorStrip(textArea)

    val searchListener = DefaultSearchListener(textArea)
    val findToolBar = FindToolBar(searchListener)
    val replaceToolBar = ReplaceToolBar(searchListener)

    val actionShowFindToolBar = rootPanel.addBottomComponent(KeyStroke.getKeyStroke(KeyEvent.VK_F, KeyEvent.CTRL_DOWN_MASK), findToolBar)
    val actionShowReplaceToolBar = rootPanel.addBottomComponent(KeyStroke.getKeyStroke("ctrl R"), replaceToolBar)

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

        rootPanel.add(viewPort)
        contentPane.add(errorStrip, BorderLayout.LINE_END)
        contentPane.add(rootPanel)

        actionShowFindToolBar.activeKeyboardOn(contentPane as JComponent)
        actionShowReplaceToolBar.activeKeyboardOn(contentPane as JComponent)

        //org.fife.rsta.ui.DocumentMap docMap = new org.fife.rsta.ui.DocumentMap(textArea);
        //contentPane.add(docMap, BorderLayout.LINE_END);
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

private fun Action.activeKeyboardOn(jComponent: JComponent) {
    jComponent.registerKeyboardAction(this, getValue(Action.ACCELERATOR_KEY) as KeyStroke,
            JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT or JComponent.WHEN_FOCUSED)
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
                    val (elements, issues) = IEC61131Facade.fileResolve(stream, false)
                    EVENT_BUS.post(ShowOverview(StOverviewTransformer(this@STEditor).create(elements)))
                    issues.forEach {
                        result.addNotice(DefaultParserNotice(this, it.message,
                                it.startLine, it.startOffset, it.length))
                    }
                    problemList.set(this@STEditor, issues)

                } catch (e: SyntaxErrorReporter.ParserException) {
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

class StOverviewTransformer(val editor: CodeEditor) {
    private val colors: Colors by editor.lookup.with()

    companion object {
        private val ICON_SIZE = 12
        private val ROOT_ICON: Icon = IconFontSwing.buildIcon(FontAwesomeRegular.FILE_CODE, ICON_SIZE.toFloat())
        private val ICON_GVL: Icon? = StructureTypeIcon.buildIcon("v", ICON_SIZE)
        private val ICON_DATATYPES: Icon? = StructureTypeIcon.buildIcon("v", ICON_SIZE)
        private val ICON_DATATYPE: Icon? = StructureTypeIcon.buildIcon("v", ICON_SIZE)
        private val ICON_METHOD: Icon? = StructureTypeIcon.buildIcon("m", ICON_SIZE)
        private val ICON_CLASS: Icon? = StructureTypeIcon.buildIcon("c", ICON_SIZE)

        private val ICON_PROGRAM: Icon? = StructureTypeIcon.buildIcon("p", ICON_SIZE)
        private val ICON_FBD: Icon? = StructureTypeIcon.buildIcon("fbd", ICON_SIZE)
        private val ICON_VAR: Icon? = StructureTypeIcon.buildIcon("v", ICON_SIZE)
        private val ICON_FUNCTION: Icon? = StructureTypeIcon.buildIcon("f", ICON_SIZE)


    }

    fun create(elements: PouElements): OverviewStructureNode {
        val root = OverviewStructureNode(StructureData(editor.titleText.trim('*'), editor, ROOT_ICON))
        val v = Visitor()
        elements.mapNotNull { it.accept(v) }.forEach { root.add(it) }
        return root
    }

    inner class Visitor : AstVisitor<OverviewStructureNode?>() {


        override fun defaultVisit(obj: Any): OverviewStructureNode? = null

        override fun visit(gvlDecl: GlobalVariableListDeclaration): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData("global variables", editor, ICON_GVL))
            gvlDecl.scope.accept(this)?.seq?.also { node.seq.addAll(it) }
            return node
        }

        override fun visit(programDeclaration: ProgramDeclaration): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData(programDeclaration.name, editor, ICON_PROGRAM))
            val variables = programDeclaration.scope.accept(this)?.seq
            val actions = programDeclaration.actions.mapNotNull { it.accept(this) }
            variables?.also { node.seq.addAll(it) }
            actions.forEach { node.seq.add(it) }
            return node
        }

        override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData(functionBlockDeclaration.name, editor, ICON_FBD))
            val variables = functionBlockDeclaration.scope.accept(this)?.seq
            val actions = functionBlockDeclaration.actions.mapNotNull { it.accept(this) }
            variables?.also { seq -> seq.forEach { node.add(it) } }
            actions.forEach { node.add(it) }
            return node
        }

        override fun visit(functionDeclaration: FunctionDeclaration): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData(functionDeclaration.name, editor, ICON_FUNCTION))
            functionDeclaration.scope.accept(this)?.seq?.also { node.seq.addAll(it) }
            return node
        }

        override fun visit(localScope: Scope): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData("Variables", editor, ICON_VAR))
            localScope.mapNotNull { it.accept(this) }.forEach { node.add(it) }
            return node
        }

        override fun visit(typeDeclarations: TypeDeclarations): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData("Data Types", editor,
                    ICON_DATATYPES, typeDeclarations.startPosition))
            typeDeclarations.mapNotNull {
                OverviewStructureNode(StructureData(it.name, editor, ICON_DATATYPE, it.startPosition))
            }
                    .forEach { node.add(it) }
            return node
        }

        override fun visit(clazz: ClassDeclaration): OverviewStructureNode? {
            val node = OverviewStructureNode(StructureData(clazz.name, editor,
                    ICON_CLASS, clazz.startPosition))

            val variables = clazz.scope.accept(this)?.seq
            variables?.also { seq -> seq.forEach { node.add(it) } }

            clazz.methods.mapNotNull {
                it.accept(this)
            }.forEach { node.add(it) }

            return node
        }

        override fun visit(variableDeclaration: VariableDeclaration): OverviewStructureNode? {
            return OverviewStructureNode(
                    StructureData("${variableDeclaration.name} : ${variableDeclaration.dataType}",
                            editor, ICON_METHOD, variableDeclaration.startPosition))
        }

        override fun visit(method: MethodDeclaration): OverviewStructureNode? {
            return OverviewStructureNode(StructureData(method.name, editor, ICON_METHOD, method.startPosition))
        }
    }
}

class TTOverviewTransformer(val editor: CodeEditor) {
    private val colors: Colors by editor.lookup.with()

    companion object {
        private val ICON_SIZE = 12
        private val ROOT_ICON: Icon = IconFontSwing.buildIcon(FontAwesomeRegular.FILE_CODE, ICON_SIZE.toFloat())
        private val ICON_GVL: Icon? = StructureTypeIcon.buildIcon("v", ICON_SIZE)
        private val ICON_DATATYPES: Icon? = StructureTypeIcon.buildIcon("v", ICON_SIZE)
        private val ICON_DATATYPE: Icon? = StructureTypeIcon.buildIcon("v", ICON_SIZE)
        private val ICON_METHOD: Icon? = StructureTypeIcon.buildIcon("m", ICON_SIZE)
        private val ICON_CLASS: Icon? = StructureTypeIcon.buildIcon("c", ICON_SIZE)

        private val ICON_PROGRAM: Icon? = StructureTypeIcon.buildIcon("p", ICON_SIZE)
        private val ICON_FBD: Icon? = StructureTypeIcon.buildIcon("fbd", ICON_SIZE)
        private val ICON_VAR: Icon? = StructureTypeIcon.buildIcon("v", ICON_SIZE)
        private val ICON_FUNCTION: Icon? = StructureTypeIcon.buildIcon("f", ICON_SIZE)


    }

    fun create(gtt: TestTableLanguageParser.FileContext): OverviewStructureNode {
        val visitor = Visitor()
        return gtt.accept(visitor)!!
    }

    inner class Visitor : TestTableLanguageBaseVisitor<OverviewStructureNode?>() {
        override fun visitFile(ctx: TestTableLanguageParser.FileContext): OverviewStructureNode {
            val root = OverviewStructureNode(StructureData(editor.titleText.trim('*'), editor, ROOT_ICON))
            ctx.table().mapAndAddTo(root)
            return root
        }

        override fun visitTable(ctx: TestTableLanguageParser.TableContext): OverviewStructureNode? {
            val root = OverviewStructureNode(StructureData(ctx.IDENTIFIER().text, editor, ROOT_ICON))
            ctx.freeVariable().mapAndAddTo(root)
            ctx.signature().mapAndUnpackTo(root)
            ctx.opts()?.accept(this)?.also { root.add(it) }
            ctx.group().accept(this)?.also { root.add(it) }
            ctx.function().mapAndAddTo(root)
            return root
        }

        override fun visitOpts(ctx: TestTableLanguageParser.OptsContext): OverviewStructureNode {
            val root = OverviewStructureNode(StructureData("Options", editor, ROOT_ICON))
            ctx.kv().forEach {
                val n = OverviewStructureNode(StructureData(it.key.text, editor, ROOT_ICON, Position.start(it.key)))
                root.add(n)
            }
            return root
        }

        override fun visitFreeVariable(ctx: TestTableLanguageParser.FreeVariableContext): OverviewStructureNode {
            return OverviewStructureNode(StructureData(ctx.name.text + " : " + ctx.dt.text,
                    editor, null, Position.start(ctx.start)))
        }

        override fun visitSignature(ctx: TestTableLanguageParser.SignatureContext): OverviewStructureNode {
            val root = OverviewStructureNode(StructureData(""))
            ctx.variableDefinition().forEach {
                root.add(OverviewStructureNode(StructureData(it.text + " : " + ctx.dt.text,
                        editor, null, Position.start(it.start))))
            }
            return root
        }

        override fun visitFunction(ctx: TestTableLanguageParser.FunctionContext): OverviewStructureNode {
            val (_, name, _) = ctx.text.split(' ', limit = 3)
            return OverviewStructureNode(StructureData(name, editor, null,
                    Position.start(ctx.start)))
        }

        private fun <E : ParserRuleContext> MutableList<E>.mapAndUnpackTo(root: OverviewStructureNode) {
            mapNotNull { it.accept(this@Visitor) }.forEach {
                it.seq.forEach { c -> root.add(c) }
            }
        }

        private fun <E : ParserRuleContext> MutableList<E>.mapAndAddTo(root: OverviewStructureNode) {
            mapNotNull { it.accept(this@Visitor) }.forEach { root.add(it) }
        }
    }
}


object StructureTypeIcon {
    fun buildIcon(text: String, size: Int, circleColor: Color = Color.LIGHT_GRAY): Icon {
        val image = BufferedImage(size, size, BufferedImage.TYPE_INT_ARGB)
        image.createGraphics().run {
            setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON)
            color = circleColor
            fillOval(0, 0, size, size)
            //TODO font = editorFont
            color = Color.black
            drawCenteredString(text, Rectangle(2, 2, size - 2, size / 2))
        }
        return ImageIcon(image)
    }


    /**
     * Draw a String centered in the middle of a Rectangle.
     *
     * @param g The Graphics instance.
     * @param text The String to draw.
     * @param rect The Rectangle to center the text in.
     */
    fun Graphics2D.drawCenteredString(text: String, rect: Rectangle) {
        // Determine the X coordinate for the text
        val x = rect.x + (rect.width - fontMetrics.stringWidth(text)) / 2
        // Determine the Y coordinate for the text (note we add the ascent, as in java 2d 0 is top of the screen)
        val y = rect.y + ((rect.height - fontMetrics.height) / 2) + fontMetrics.ascent
        // Draw the String
        drawString(text, x, y)
    }

}

class TTEditor(lookup: Lookup) : CodeEditor(lookup) {
    val editorId = "" + Math.random()
    val timer = Timer(500) { _ -> EVENT_BUS.post(EventGetetaUpdate(textArea.text)) }
    val problemList by super.lookup.with<ProblemList>()

    init {
        languageSupport = TestTableLanguageSupport(lookup)

        textArea.addParser(object : AbstractParser() {
            override fun parse(doc: RSyntaxDocument?, style: String?): ParseResult {
                val res = DefaultParseResult(this)
                val parser = GetetaFacade.createParser(CharStreams.fromReader(DocumentReader(doc)))
                //parser.errorReporter.isPrint = true
                try {
                    val ctx = parser.file()
                    parser.errorReporter.throwException()
                    val node = TTOverviewTransformer(this@TTEditor).create(ctx)
                    EVENT_BUS.post(ShowOverview(node))
                    problemList.set(this@TTEditor, listOf())
                } catch (e: SyntaxErrorReporter.ParserException) {
                    e.errors.forEach {
                        res.addNotice(DefaultParserNotice(this, it.msg,
                                it.line, it.offendingSymbol?.startIndex ?: -1,
                                it.offendingSymbol?.text?.length ?: -1))
                    }
                }
                return res
            }
        })

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
