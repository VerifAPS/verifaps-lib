package edu.kit.iti.formal.automation.ide.tools

import edu.kit.iti.formal.automation.ide.*
import edu.kit.iti.formal.automation.st.ast.Position
import java.awt.*
import java.awt.event.KeyAdapter
import java.awt.event.KeyEvent
import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent
import java.awt.image.BufferedImage
import java.util.*
import javax.swing.*
import javax.swing.tree.DefaultTreeCellRenderer
import javax.swing.tree.DefaultTreeModel
import javax.swing.tree.TreeNode
import javax.swing.tree.TreePath

interface OutlineService {
    fun show(node: OverviewStructureNode)
}

class OverviewPanel(val lookup: Lookup) : ToolPane("overview"), OutlineService {
    val tree = JTree()

    init {
        val root = contentPane as JPanel
        root.layout = BorderLayout()
        root.add(JScrollPane(tree))
        titleText = "Overview"
        titleIcon = IconFontSwing.buildIcon(FontAwesomeRegular.EYE, 12f)
        tree.model = DefaultTreeModel(null)
        tree.cellRenderer = CellRenderer

        tree.addMouseListener(object : MouseAdapter() {
            override fun mouseClicked(e: MouseEvent) {
                val path = tree.ui.getClosestPathForLocation(tree, e.x, e.y)
                tree.selectionPath = path
                jumpTo()
            }
        })

        tree.addKeyListener(object : KeyAdapter() {
            override fun keyTyped(e: KeyEvent) {
                if (e.keyCode == KeyEvent.VK_ENTER) {
                    jumpTo()
                    e.consume()
                }
            }
        })

    }

    override fun show(evt: OverviewStructureNode) {
        tree.model = DefaultTreeModel(evt)
        tree.expandSubTree(TreePath(evt))
    }

    object CellRenderer : DefaultTreeCellRenderer() {
        override fun getTreeCellRendererComponent(tree: JTree?, value: Any, sel: Boolean, expanded: Boolean, leaf: Boolean, row: Int, hasFocus: Boolean): Component {
            val data = (value as OverviewStructureNode).data
            val lbl = super.getTreeCellRendererComponent(tree, data.text, sel, expanded, leaf, row, hasFocus) as JLabel
            //lbl.font = editorFont
            lbl.font = lbl.font.deriveFont(data.fontStyle)
            lbl.foreground = data.fgColor ?: lbl.foreground
            lbl.background = data.fgColor ?: lbl.background
            lbl.icon = data.icon
            return lbl
        }
    }

    fun jumpTo(node: OverviewStructureNode) {
        val editor = node.data.editor
        val position = node.data.caretPosition

        if (editor != null && position != null) {
            lookup.get<JumpService>().jumpTo(editor, position)
        }
    }

    fun jumpTo() = tree.selectionPath?.lastPathComponent?.let {
        jumpTo(it as OverviewStructureNode)
    }
}


open class DefaultTreeNode<T>(
        val data: T,
        val seq: MutableList<DefaultTreeNode<T>> = arrayListOf(),
        private var _parent: DefaultTreeNode<T>? = null) : TreeNode {
    override fun children(): Enumeration<out TreeNode> = Collections.enumeration(seq)
    override fun isLeaf(): Boolean = seq.isEmpty()
    override fun getChildCount(): Int = seq.size
    override fun getParent(): TreeNode? = _parent
    override fun getChildAt(childIndex: Int): TreeNode = seq[childIndex]
    override fun getIndex(node: TreeNode?): Int = seq.indexOf(node)
    override fun getAllowsChildren(): Boolean = false
    fun add(node: DefaultTreeNode<T>) {
        seq.add(node)
        node._parent = this
    }
}

typealias OverviewStructureNode = DefaultTreeNode<StructureData>

data class StructureData(
        val text: String,
        val editor: CodeEditor? = null,
        val icon: Icon? = null,
        val caretPosition: Position? = null,
        val fgColor: Color? = null,
        val bgColor: Color? = null,
        val fontStyle: Int = 0)


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
