package edu.kit.iti.formal.automation.ide

import edu.kit.iti.formal.automation.analysis.ReportCategory
import edu.kit.iti.formal.automation.analysis.ReportLevel
import edu.kit.iti.formal.automation.analysis.ReporterMessage
import edu.kit.iti.formal.automation.st.ast.Position
import java.awt.BorderLayout
import java.awt.Component
import javax.swing.*
import javax.swing.table.AbstractTableModel
import javax.swing.table.DefaultTableCellRenderer

public class Problem(
        val message: ReporterMessage,
        val editorId: String
)

public class ProblemList : AbstractTableModel() {
    private val seq = arrayListOf<Problem>()
    private val COLUMNS = listOf<String>(
            "File", "Message", "Position", "Category", "Level"
    )

    fun add(editorId: String, msgs: Collection<ReporterMessage>) {
        val oldSize = seq.size
        msgs.forEach { seq += Problem(it, editorId) }
        fireTableDataChanged()
    }

    fun remove(editorId: String, msgs: Collection<ReporterMessage>) {
        val old = seq.filter { it.editorId == editorId }
        seq.removeAll(old)
        fireTableDataChanged()

    }

    fun set(editorId: String, msgs: Collection<ReporterMessage>) {
        val old = seq.filter { it.editorId == editorId }
        seq.removeAll(old)
        msgs.forEach { seq += Problem(it, editorId) }
        fireTableDataChanged()
    }

    override fun getRowCount(): Int = seq.size
    override fun getColumnCount(): Int = COLUMNS.size
    override fun getValueAt(rowIndex: Int, columnIndex: Int): Any {
        val msg = seq[rowIndex].message
        return when (columnIndex) {
            0 -> msg.component1()
            1 -> msg.component2()
            2 -> msg.component3()
            4 -> msg.component5()
            5 -> msg.component6()
            else -> ""
        }
    }

    override fun getColumnClass(columnIndex: Int): Class<*> {
        return when (columnIndex) {
            2 -> Position::class.java
            3 -> ReportCategory::class.java
            4 -> ReportLevel::class.java
            else -> String::class.java
        }
    }

    override fun findColumn(columnName: String?): Int = COLUMNS.indexOf(columnName)
    override fun getColumnName(column: Int): String = COLUMNS[column]
}

public class ProblemPanel(lookup: Lookup) : ToolPane() {
    val lookup = Lookup(lookup)
    val problems by lookup.with<ProblemList>()
    val listProblems = JTable(problems)
    val scrollPane = JScrollPane(listProblems)
    val toolbar = JToolBar()


    init {
        title = "Problems"
        listProblems.model = problems
        listProblems.setDefaultRenderer(Position::class.java,
                object : DefaultTableCellRenderer() {
                    override fun getTableCellRendererComponent(table: JTable?, value: Any?, isSelected: Boolean, hasFocus: Boolean, row: Int, column: Int): Component {
                        val pos = value as Position?
                        return super.getTableCellRendererComponent(table, value, isSelected, hasFocus, row, column)
                    }
                })

        listProblems.setDefaultRenderer(Position::class.java,
                object : DefaultTableCellRenderer() {
                    override fun getTableCellRendererComponent(table: JTable?, value: Any?, isSelected: Boolean, hasFocus: Boolean, row: Int, column: Int): Component {
                        val pos = value as Position?
                        return super.getTableCellRendererComponent(table, value, isSelected, hasFocus, row, column)
                    }
                })

        add(toolbar, BorderLayout.NORTH)
        add(scrollPane)
    }

    override fun close() {}
}