package edu.kit.iti.formal.automation.ide

import com.vlsolutions.swing.docking.DockKey
import com.vlsolutions.swing.docking.Dockable
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.*
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
import org.netbeans.swing.outline.DefaultOutlineModel
import org.netbeans.swing.outline.Outline
import org.netbeans.swing.outline.RenderDataProvider
import org.netbeans.swing.outline.RowModel
import java.awt.*
import java.io.File
import java.io.StringWriter
import javax.swing.*
import javax.swing.event.DocumentEvent
import javax.swing.event.DocumentListener
import javax.swing.event.EventListenerList
import javax.swing.event.TreeModelListener
import javax.swing.table.AbstractTableModel
import javax.swing.table.DefaultTableCellRenderer
import javax.swing.tree.TreeModel
import javax.swing.tree.TreePath
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


abstract class TabbedPanel() : JPanel(true), Closeable, Dockable {
    val _dockKey = DockKey(Math.random().toString())

    constructor(l: LayoutManager) : this() {
        layout = l
        title = "UNKNOWN"
    }

    var title: String? = null
        set(value) {
            firePropertyChange("title", field, value)
            field = value
            _dockKey.tabName = value
            _dockKey.name = value
        }

    var icon: Icon? = null
        set(value) {
            _dockKey.icon = value
            firePropertyChange("icon", field, value)
            field = value
        }

    var tip: String? = null
        set(value) {
            _dockKey.tooltip = tip
            firePropertyChange("tip", field, value)
            field = value
        }


    override fun getComponent(): Component = this
    override fun getDockKey(): DockKey = _dockKey
}

/**
 *
 * @author Alexander Weigl
 * @version 1 (11.03.19)
 */
abstract class EditorPane : TabbedPanel(), Saveable, HasFont {
    abstract val languageSupport: LanguageSupport<*>

    var file: File? by Delegates.observable<File?>(null) { prop, old, new ->
        firePropertyChange(prop.name, old, new)
    }

    override fun close() {
        //DockingManager.undock(dockable)
    }

    abstract override var textFont: Font

    init {
        addPropertyChangeListener("file") { evt ->
            if (evt.newValue != null)
                title = (evt.newValue as File).name
        }
    }

    abstract override fun save()
    abstract override fun saveAs()
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

        _dockKey.isCloseEnabled = true
        _dockKey.isFloatEnabled = false
        _dockKey.isAutoHideEnabled = false
        _dockKey.isNotification = false
        _dockKey.isMaximizeEnabled = true
    }
}

class TTEditor(lookup: Lookup) : CodeEditor(lookup) {
    val splitPane = JSplitPane(JSplitPane.HORIZONTAL_SPLIT)
    //var swingbox = org.xhtmlrenderer.simple.XHTMLPanel()
    //var swingbox = JEditorPane()
    var swingbox = Outline()
    val viewRender = JScrollPane(swingbox)

    val timer = Timer(500) { e -> render() }

    fun render() {
        try {
            val gtt = GetetaFacade.parseTableDSL(textArea.text)
            val ioCompare = compareBy<ProgramVariable> { it.io }
            val nameCompare = compareBy<ProgramVariable> { it.name }
            val cmp = ioCompare.thenComparing(nameCompare)
            val vars = gtt.programVariables.toMutableList()
            vars.sortWith(cmp)
            val treeModel = TTTableModel(gtt)
            val rowModel = TTRowModel(vars)
            val mdl = DefaultOutlineModel.createOutlineModel(
                    treeModel, rowModel, true, "Groups")
            swingbox.model = mdl
            swingbox.isRootVisible = true


            /*val sw = StringWriter()
            val pp = HTMLTablePrinter(gtt, CodeWriter(sw))
            pp.printPreamble()
            pp.print()
            pp.printPostamble()
            print(sw.toString())
            swingbox.text = sw.toString()*/
            /*swingbox.setDocumentFromString(sw.toString(),
                    File(".").toURI().toString(),
                    XhtmlNamespaceHandler())
                    */
        } catch (e: Exception) {
        }
    }

    init {
        languageSupport = TestTableLanguageSupport(lookup)

        splitPane.resizeWeight = 1.0
        splitPane.dividerLocation = (0.7 * width).toInt()

        swingbox.setDefaultRenderer(TestTableLanguageParser.CellContext::class.java,
                object : DefaultTableCellRenderer() {
                    override fun getTableCellRendererComponent(table: JTable?, value: Any?, isSelected: Boolean,
                                                               hasFocus: Boolean, row: Int, column: Int): Component {
                        val ctx =
                                when (value) {
                                    is TestTableLanguageParser.CellContext -> value.text
                                    is TableNode -> value.id
                                    else -> value.toString()
                                }
                        return super.getTableCellRendererComponent(table, ctx, isSelected, hasFocus, row, column)
                    }
                })

        swingbox.renderDataProvider = object : RenderDataProvider {
            override fun getTooltipText(o: Any?): String = ""
            override fun getIcon(o: Any?): Icon? = null
            override fun getBackground(o: Any?): Color = Color.WHITE
            override fun getDisplayName(o: Any?): String = when (o) {
                is TableNode -> o.id
                else -> ""
            }

            override fun getForeground(o: Any?): Color = Color.black
            override fun isHtmlDisplayName(o: Any?): Boolean = false
        }

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

class TTRowModel(val columns: List<ProgramVariable>) : RowModel {
    override fun getValueFor(node: Any?, column: Int): Any {
        if (column == 0 && node is TableNode) {
            return node.duration.repr()
        }
        if (node is TableRow) {
            val c = columns[column - 1]
            return node.rawFields[c] ?: ""
        }
        return ""
    }

    override fun setValueFor(node: Any?, column: Int, value: Any?) {}
    override fun isCellEditable(node: Any?, column: Int): Boolean = false
    override fun getColumnName(column: Int): String = when (column) {
        0 -> "Duration"
        else -> columns[column - 1].name
    }

    override fun getColumnClass(column: Int): Class<*> = TestTableLanguageParser.CellContext::class.java
    override fun getColumnCount(): Int = 1 + columns.size
}

class TTTableModel(val gtt: GeneralizedTestTable) : TreeModel {
    protected var listenerList: EventListenerList = EventListenerList()

    override fun getRoot() = gtt.region
    override fun isLeaf(node: Any?): Boolean = node !is Region
    override fun getChildCount(parent: Any?): Int = if (parent is Region) parent.children.size else 0
    override fun removeTreeModelListener(l: TreeModelListener?) = listenerList.add(TreeModelListener::class.java, l)
    override fun addTreeModelListener(l: TreeModelListener?) = listenerList.add(TreeModelListener::class.java, l)

    override fun valueForPathChanged(path: TreePath?, newValue: Any?) {
        println("listenerList = ${listenerList}")
    }

    override fun getIndexOfChild(parent: Any?, child: Any?): Int {
        if (parent is Region && child is TableNode) {
            return parent.children.indexOf(child)
        }
        return -1
    }

    override fun getChild(parent: Any?, index: Int): Any? {
        if (parent is Region) return parent.children[index]
        return null
    }
}

open class MyTableModel<T>(rows: Int, cols: Int) : AbstractTableModel() {
    var _rowCount = rows
        set(value) {
            field = value
            ensureCells()
        }

    var _colCount = cols
        set(value) {
            field = value
            ensureCells()
        }

    val values = ArrayList<ArrayList<T?>>()

    fun ensureCells() {
        values.ensureCapacity(rowCount)
        while (values.size < rowCount) {
            values.add(ArrayList(columnCount))
        }
        values.forEach { row -> while (row.size < columnCount) row.add(null) }
    }

    override fun getRowCount(): Int = _rowCount
    override fun getColumnCount(): Int = _colCount

    override fun getValueAt(rowIndex: Int, columnIndex: Int): Any? {
        ensureCells()
        return values[rowIndex][columnIndex]
    }
}
