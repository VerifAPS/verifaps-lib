package edu.kit.iti.formal.automation.ide.tools

import edu.kit.iti.formal.automation.ide.EVENT_BUS
import edu.kit.iti.formal.automation.ide.EventGetetaUpdate
import edu.kit.iti.formal.automation.ide.Lookup
import edu.kit.iti.formal.automation.ide.ToolPane
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.*
import org.netbeans.swing.outline.DefaultOutlineModel
import org.netbeans.swing.outline.Outline
import org.netbeans.swing.outline.RenderDataProvider
import org.netbeans.swing.outline.RowModel
import java.awt.BorderLayout
import java.awt.Color
import java.awt.Component
import javax.swing.Icon
import javax.swing.JScrollPane
import javax.swing.JTable
import javax.swing.event.EventListenerList
import javax.swing.event.TreeModelListener
import javax.swing.table.AbstractTableModel
import javax.swing.table.DefaultTableCellRenderer
import javax.swing.tree.TreeModel
import javax.swing.tree.TreePath


class GetetaPreview(val lookup: Lookup) : ToolPane("geteta-preview") {
    val outline = Outline()
    val viewRender = JScrollPane(outline)

    init {
        contentPane.layout = BorderLayout()
        contentPane.add(viewRender)
        titleText = "Test Table Preview"
        EVENT_BUS.listenTo(this::render)

        outline.setDefaultRenderer(TestTableLanguageParser.CellContext::class.java,
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

        outline.renderDataProvider = object : RenderDataProvider {
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

    fun render(event: EventGetetaUpdate) {
        try {
            val gtt = GetetaFacade.parseTableDSL(event.text)
            val ioCompare = compareBy<ProgramVariable> { it.io }
            val nameCompare = compareBy<ProgramVariable> { it.name }
            val cmp = ioCompare.thenComparing(nameCompare)
            val vars = gtt.programVariables.toMutableList()
            vars.sortWith(cmp)
            val treeModel = TTTableModel(gtt)
            val rowModel = TTRowModel(vars)
            val mdl = DefaultOutlineModel.createOutlineModel(
                    treeModel, rowModel, true, "Groups")
            outline.model = mdl
            outline.isRootVisible = true
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
