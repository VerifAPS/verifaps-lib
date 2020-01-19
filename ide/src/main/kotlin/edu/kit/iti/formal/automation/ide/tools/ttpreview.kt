package edu.kit.iti.formal.automation.ide.tools

import edu.kit.iti.formal.automation.ide.JumpService
import edu.kit.iti.formal.automation.ide.Lookup
import edu.kit.iti.formal.automation.ide.ToolPane
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.*
import org.antlr.v4.runtime.ParserRuleContext
import org.netbeans.swing.outline.DefaultOutlineModel
import org.netbeans.swing.outline.Outline
import org.netbeans.swing.outline.RenderDataProvider
import org.netbeans.swing.outline.RowModel
import java.awt.BorderLayout
import java.awt.Color
import java.awt.Component
import java.awt.Font
import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent
import javax.swing.*
import javax.swing.event.EventListenerList
import javax.swing.event.TreeModelListener
import javax.swing.table.AbstractTableModel
import javax.swing.table.DefaultTableCellRenderer
import javax.swing.table.TableCellRenderer
import javax.swing.tree.TreeModel
import javax.swing.tree.TreePath

private val FONT = Font(Font.MONOSPACED, 0, 14)

interface GetetaPreviewService {
    fun render(text: List<GeneralizedTestTable>)
    fun select(tableName: String)
}

class GetetaPreview(val lookup: Lookup) : ToolPane("geteta-preview"), GetetaPreviewService {
    private val headerRenderer: TableCellRenderer
    private var renderDataProvider: RenderDataProvider
    private var tableCellRenderer: DefaultTableCellRenderer
    val rootPane = JTabbedPane()
    //val outline = Outline()
    //val viewRender = JScrollPane(outline)

    init {
        contentPane.layout = BorderLayout()
        contentPane.add(rootPane)
        titleText = "Test Table Preview"

        headerRenderer = object : DefaultTableCellRenderer() {
            override fun getTableCellRendererComponent(table: JTable?, value: Any?, isSelected: Boolean, hasFocus: Boolean, row: Int, column: Int): Component {
                val lbl = super.getTableCellRendererComponent(table, value, isSelected, hasFocus, row, column) as JLabel
                lbl.horizontalAlignment = JLabel.CENTER
                lbl.font = FONT.deriveFont(Font.BOLD)
                return lbl
            }
        }

        //outline.setDefaultRenderer(TestTableLanguageParser.CellContext::class.java,
        tableCellRenderer = object : DefaultTableCellRenderer() {
            override fun getTableCellRendererComponent(table: JTable?, value: Any?, isSelected: Boolean,
                                                       hasFocus: Boolean, row: Int, column: Int): Component {
                val ctx =
                        when (value) {
                            is TestTableLanguageParser.CellContext -> value.text
                            is TableNode -> value.id
                            else -> value.toString()
                        }
                val lbl = super.getTableCellRendererComponent(table, ctx, isSelected, hasFocus, row, column) as JLabel
                lbl.horizontalAlignment = JLabel.CENTER
                lbl.font = FONT
                return lbl
            }
        }

        //outline.renderDataProvider =
        renderDataProvider = object : RenderDataProvider {
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
    }

    override fun render(gtts: List<GeneralizedTestTable>) {
        val selectedIndex = rootPane.selectedIndex
        ((rootPane.tabCount - 1) downTo 0).forEach { rootPane.removeTabAt(it) }
        gtts.forEach(this::render)
        rootPane.selectedIndex = selectedIndex
    }

    override fun select(tableName: String) {
        val titles = (0 until rootPane.tabCount).map { rootPane.getTitleAt(it) }
        val index = titles.indexOf(tableName)
        if (index >= 0)
            rootPane.selectedIndex = index
    }

    fun render(gtt: GeneralizedTestTable) {
        val outline = Outline()
        val scrollPane = JScrollPane(outline)

        outline.renderDataProvider = renderDataProvider
        outline.setDefaultRenderer(TestTableLanguageParser.CellContext::class.java, tableCellRenderer)
        rootPane.addTab(gtt.name, scrollPane)
        outline.setSelectionMode(ListSelectionModel.SINGLE_SELECTION)
        outline.cellSelectionEnabled = true

        try {
            val ioCompare = compareBy<ProgramVariable> { it.category }
            val nameCompare = compareBy<ProgramVariable> { it.name }
            val cmp = ioCompare.thenComparing(nameCompare)
            val vars = gtt.programVariables.filterIsInstance<ProgramVariable>().toMutableList()
            vars.sortWith(cmp)
            val treeModel = TTTableModel(gtt)
            val rowModel = TTRowModel(vars)
            val mdl = DefaultOutlineModel.createOutlineModel(
                    treeModel, rowModel, true, "Groups")
            outline.model = mdl
            outline.isRootVisible = true

            outline.addMouseListener(object : MouseAdapter() {
                override fun mouseClicked(e: MouseEvent) {
                    if (e.clickCount == 2) {
                        val sc = outline.selectedColumn
                        val sr = outline.selectedRow
                        val ctx = outline.getValueAt(sr, sc) as? ParserRuleContext
                        if (ctx == null) return;
                        val name = ctx.start.tokenSource.sourceName
                        if (e.isControlDown) {
                            //lookup.get<JumpService>().changeInEditor(name, ctx.start.startIndex, ctx.stop.stopIndex + 1)
                        } else {
                            lookup.get<JumpService>().selectInEditor(name, ctx.start.startIndex, ctx.stop.stopIndex + 1)
                        }
                    }
                }
            })


            (0 until outline.columnCount).forEach { ci ->
                val n = rowModel.getColumnName(ci)
                outline.getColumn(n)?.also {
                    it.headerRenderer = this.headerRenderer
                }
            }
        } catch (e: Exception) {
        }
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
