package edu.kit.iti.formal.automation.ide

import edu.kit.iti.formal.automation.analysis.ReportCategory
import edu.kit.iti.formal.automation.analysis.ReportLevel
import edu.kit.iti.formal.automation.analysis.ReporterMessage
import edu.kit.iti.formal.automation.st.ast.Position
import org.antlr.v4.runtime.ParserRuleContext
import org.netbeans.swing.outline.*
import java.awt.Color
import java.awt.Component
import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent
import java.util.*
import javax.swing.*
import javax.swing.table.DefaultTableCellRenderer
import javax.swing.tree.DefaultTreeModel
import javax.swing.tree.TreeNode
import javax.swing.tree.TreePath
import kotlin.collections.HashMap


typealias Problem = ReporterMessage

interface ProblemService {
    fun clearProblems(identity: Any)
    fun announceProblems(identity: Any, problems: Iterable<Problem>)
    fun registerListener(listener: () -> Unit)
}

private class ProblemModel : ProblemService {
    private val listeners = arrayListOf<() -> Unit>()
    private val map = HashMap<Any, List<Problem>>()
    private val allCurrentProblems = arrayListOf<Problem>()
            .also { it.ensureCapacity(1024) }

    private val defaultRowModel = ProblemRowModel()

    fun sortByFile(): OutlineModel {
        val sub = allCurrentProblems.groupBy { it.sourceName }
                .map { (cat, seq) ->
                    ProblemCatNode(cat,
                            seq.sortedBy { it.startLine }
                                    .map { ProblemTreeNode(it) })
                }
        val rootOfAllProblems = TreeReadOnlyNode(sub)
        val treeModel = DefaultTreeModel(rootOfAllProblems)
        return DefaultOutlineModel.createOutlineModel(treeModel, defaultRowModel)
    }

    override fun clearProblems(identity: Any) {
        map.remove(identity)?.let {
            allCurrentProblems.removeAll(it.toSet())
        }
        listeners.forEach { it() }
    }

    override fun announceProblems(identity: Any, problems: Iterable<Problem>) {
        map.remove(identity)?.let { allCurrentProblems.removeAll(it.toSet()) }
        val s = problems.toList()
        map[identity] = s
        allCurrentProblems.addAll(s)
        listeners.forEach { it() }
    }

    override fun registerListener(listener: () -> Unit) {
        listeners.add(listener)
    }
}

open class TreeLeafNode : TreeNode {
    var _parent: TreeNode? = null
    override fun children(): Enumeration<out TreeNode> = Collections.emptyEnumeration()
    override fun isLeaf(): Boolean = true
    override fun getChildCount(): Int = 0
    override fun getParent(): TreeNode? = _parent
    override fun getChildAt(childIndex: Int) = null
    override fun getIndex(node: TreeNode?) = -1
    override fun getAllowsChildren(): Boolean = false
}

open class TreeReadOnlyNode(val children: List<TreeNode> = listOf()) : TreeNode {
    var _parent: TreeNode? = null
    override fun children(): Enumeration<out TreeNode> = Collections.enumeration(children)
    override fun isLeaf() = children.isEmpty()
    override fun getChildCount() = children.size
    override fun getParent() = _parent
    override fun getChildAt(childIndex: Int) = children[childIndex]
    override fun getIndex(node: TreeNode?) = children.indexOf(node)
    override fun getAllowsChildren() = true
}

class ProblemCatNode(val category: String, children: List<TreeNode> = listOf()) : TreeReadOnlyNode(children)
class ProblemTreeNode(val problem: Problem) : TreeLeafNode()

class ProblemRowModel : RowModel {
    private val COLUMNS = listOf("Position", "Category", "Level")

    override fun getValueFor(node: Any, column: Int): Any {
        return (node as? ProblemTreeNode)?.problem?.let { msg ->
            when (column) {
                //0 -> msg.component1()
                //1 -> msg.component2()
                0 -> msg.component3()
                1 -> msg.component5()
                2 -> msg.component6()
                else -> ""
            }
        } ?: ""
    }

    override fun getColumnClass(columnIndex: Int): Class<*> {
        return when (columnIndex) {
            0 -> Position::class.java
            1 -> ReportCategory::class.java
            2 -> ReportLevel::class.java
            else -> String::class.java
        }
    }

    override fun setValueFor(node: Any?, column: Int, value: Any?) {
        TODO("Not yet implemented")
    }

    override fun isCellEditable(node: Any?, column: Int): Boolean = false

    override fun getColumnName(column: Int): String = COLUMNS[column]

    override fun getColumnCount(): Int = COLUMNS.size
}


class ProblemPanel(lookup: Lookup) : ToolPane("problems") {
    private val jumpService by lookup.with<JumpService>()
    private val problemModel = ProblemModel()
    val listProblems = Outline()
    val scrollPane = JScrollPane(listProblems)
    //val toolbar = JToolBar()

    //val actionCopy = createAction("Copy", accel = KeyStroke.getKeyStroke("Ctrl-c")) {
    //    println("Todo")
    //}

    init {
        lookup.register<ProblemService>(problemModel)
        titleText = "Problems"

        listProblems.setSelectionMode(ListSelectionModel.SINGLE_SELECTION)
        listProblems.rowSelectionAllowed = true
        listProblems.renderDataProvider = object : RenderDataProvider {
            override fun getTooltipText(o: Any?): String = ""
            override fun getIcon(o: Any?): Icon? = null
            override fun getBackground(o: Any?): Color = Color.WHITE
            override fun getDisplayName(o: Any?): String = when (o) {
                is ProblemCatNode -> o.category
                is ProblemTreeNode -> o.problem.message
                else -> ""
            }

            override fun getForeground(o: Any?): Color = Color.black
            override fun isHtmlDisplayName(o: Any?): Boolean = false
        }
        problemModel.registerListener {
            val m = problemModel.sortByFile()
            listProblems.model = m

            setTreeExpandedState(listProblems, m)
            resizeColumnWidth(listProblems)
            /*m.treePathSupport?.addTreeExpansionListener(object : TreeExpansionListener {
                override fun treeExpanded(event: TreeExpansionEvent?) = resizeColumnWidth(listProblems)
                override fun treeCollapsed(event: TreeExpansionEvent?) {}
            })*/
        }
        listProblems.isRootVisible = false
        listProblems.autoResizeMode = JTable.AUTO_RESIZE_SUBSEQUENT_COLUMNS

        listProblems

        listProblems.setDefaultRenderer(Position::class.java,
                object : DefaultTableCellRenderer() {
                    override fun getTableCellRendererComponent(table: JTable?, value: Any?,
                                                               isSelected: Boolean, hasFocus: Boolean,
                                                               row: Int, column: Int): Component {
                        val s = when (value) {
                            is Position -> "${value.lineNumber} "
                            else -> value?.toString()
                        }
                        val lbl = super.getTableCellRendererComponent(table, s, isSelected,
                                hasFocus, row, column) as JLabel
                        when (value) {
                            is Position -> lbl.horizontalAlignment = JLabel.RIGHT
                        }
                        return lbl
                    }
                })

        listProblems.addMouseListener(object : MouseAdapter() {
            override fun mouseClicked(e: MouseEvent) {
                if (e.clickCount == 2 && e.button == MouseEvent.BUTTON1) {
                    val row = listProblems.rowAtPoint(e.point)
                    val sc = listProblems.selectedColumn
                    val sr = listProblems.selectedRow
                    val ctx = listProblems.getValueAt(sr, 1) as? Position ?: return
                    jumpService.jumpTo(ctx)
                }
            }
        })
        add(scrollPane)
    }
}

fun resizeColumnWidth(table: JTable) {
    table.autoResizeMode = JTable.AUTO_RESIZE_OFF

    for (column in 0 until table.columnCount) {
        val tableColumn = table.columnModel.getColumn(column)
        var preferredWidth = tableColumn.minWidth
        val maxWidth = tableColumn.maxWidth

        for (row in 0 until table.rowCount) {
            val cellRenderer = table.getCellRenderer(row, column)
            val c = table.prepareRenderer(cellRenderer, row, column)
            val width = c.preferredSize.width + table.intercellSpacing.width
            preferredWidth = Math.max(preferredWidth, width)

            //  We've exceeded the maximum width, no need to check other rows
            if (preferredWidth >= maxWidth) {
                preferredWidth = maxWidth
                break
            }
        }
        tableColumn.preferredWidth = preferredWidth
    }
}

fun setTreeExpandedState(o: Outline, tree: OutlineModel) {
    fun recur(p: TreePath) {
        for (i in 0 until tree.getChildCount(p.lastPathComponent)) {
            recur(p.pathByAddingChild(tree.getChild(p.lastPathComponent, i)))
        }
        o.expandPath(p)
    }
    recur(TreePath(tree.root))
}
