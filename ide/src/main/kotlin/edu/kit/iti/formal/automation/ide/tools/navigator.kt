package edu.kit.iti.formal.automation.ide.tools

import bibliothek.gui.dock.common.DefaultSingleCDockable
import edu.kit.iti.formal.automation.ide.*
import java.awt.BorderLayout
import java.awt.Component
import java.awt.Desktop
import java.awt.event.KeyEvent
import java.awt.event.MouseAdapter
import java.awt.event.MouseEvent
import java.io.File
import java.util.*
import javax.swing.*
import javax.swing.tree.DefaultTreeCellRenderer
import javax.swing.tree.DefaultTreeModel
import javax.swing.tree.TreeNode
import javax.swing.tree.TreePath
import kotlin.Comparator

interface NavigatorService {
    //fun setRootFile(root: File)
}


class FileTreePanel(val lookup: Lookup) :
        DefaultSingleCDockable("file-tree", "Navigator"),
        NavigatorService {
    val contextMenu = JPopupMenu()
    val treeFiles = JTree(DefaultTreeModel(FolderTreeNode(File("").absoluteFile, this::fileFilter)))
    val txtFolder = JTextField(File("").absolutePath)

    val actionOpenFile = createAction("Open File",
            accel = KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, 0),
            fontIcon = FontAwesomeRegular.EDIT) {
        val file = treeFiles.selectionModel.selectionPath.lastPathComponent as FolderTreeNode
        if (file.file.isDirectory)
            actionGoInto.actionPerformed(null)
        else
            lookup.get<FileOpen>().open(file.file)
    }

    val actionGoUp = createAction("Go Up",
            accel = KeyStroke.getKeyStroke(KeyEvent.VK_UP, KeyEvent.CTRL_DOWN_MASK),
            fontIcon = FontAwesomeRegular.ARROW_ALT_CIRCLE_UP) {
        val file = treeFiles.model.root as? FolderTreeNode
        if (file != null) {
            val m = DefaultTreeModel(FolderTreeNode(file.file.parentFile.absoluteFile, this::fileFilter))
            treeFiles.model = m
            txtFolder.text = file.file.absolutePath
        }
    }

    val actionGoInto = createAction("Go Into",
            accel = KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, KeyEvent.CTRL_DOWN_MASK),
            fontIcon = FontAwesomeRegular.ARROW_ALT_CIRCLE_DOWN) {
        val file = treeFiles.selectionModel?.selectionPath?.lastPathComponent as? FolderTreeNode
        if (file != null) {
            val m = DefaultTreeModel(FolderTreeNode(file.file, this::fileFilter))
            treeFiles.model = m
            txtFolder.text = file.file.absolutePath
        }
    }

    val actionExpandSubTree = createAction("Expand",
            accel = KeyStroke.getKeyStroke(KeyEvent.VK_RIGHT, KeyEvent.CTRL_DOWN_MASK),
            fontIcon = FontAwesomeRegular.ARROW_ALT_CIRCLE_RIGHT) {
        treeFiles.selectionModel?.selectionPath?.also { treeFiles.expandSubTree(it) }
    }

    val actionOpenExplorer = createAction("Open in Explorer",
            accel = KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, KeyEvent.CTRL_DOWN_MASK)) {
        val file = treeFiles.selectionModel?.selectionPath?.lastPathComponent as FolderTreeNode
        try {
            Desktop.getDesktop()?.browseFileDirectory(file.file)
        } catch (e: UnsupportedOperationException) {
            ProcessBuilder("explorer", "/select,${file.file}").start()
        }
    }

    val actionOpenSystem = createAction("Open in System",
            accel = KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, KeyEvent.CTRL_DOWN_MASK or KeyEvent.ALT_DOWN_MASK)) {
        val file = treeFiles.selectionModel?.selectionPath?.lastPathComponent as FolderTreeNode
        Desktop.getDesktop()?.open(file.file)
    }


    val actionRefresh = createAction("Refresh",
            accel = KeyStroke.getKeyStroke(KeyEvent.VK_R, KeyEvent.CTRL_DOWN_MASK)) {
        val m = treeFiles.model
        treeFiles.model = null
        treeFiles.model = m
    }

    init {
        titleIcon = IconFontSwing.buildIcon(FontAwesomeSolid.COMPASS, 12f)

        treeFiles.border = BorderFactory.createEmptyBorder(10, 10, 10, 10)

        treeFiles.addMouseListener(object : MouseAdapter() {
            override fun mouseClicked(e: MouseEvent) = mouseReleased(e)
            override fun mousePressed(e: MouseEvent) = mouseReleased(e)

            override fun mouseReleased(e: MouseEvent) {
                if (e.isPopupTrigger) {
                    val row = treeFiles.getRowForLocation(e.x, e.y)
                    if (row != -1) {
                        treeFiles.setSelectionRow(row)
                    }
                    contextMenu.show(e.component, e.x, e.y)
                }
            }
        })
        contextMenu.add(actionOpenFile)
        contextMenu.addSeparator()
        contextMenu.add(actionGoUp)
        contextMenu.add(actionGoInto)
        contextMenu.addSeparator()
        contextMenu.add(actionExpandSubTree)
        contextMenu.add(actionRefresh)
        contextMenu.addSeparator()
        contextMenu.add(actionOpenExplorer)
        contextMenu.add(actionOpenSystem)

        actionOpenFile.activateKeystroke(treeFiles)
        actionGoUp.activateKeystroke(treeFiles)
        actionGoUp.activateKeystroke(treeFiles, KeyStroke.getKeyStroke(KeyEvent.VK_BACK_SPACE, 0))
        actionGoInto.activateKeystroke(treeFiles)
        actionGoInto.activateKeystroke(treeFiles, KeyStroke.getKeyStroke(KeyEvent.VK_PERIOD, 0))
        actionExpandSubTree.activateKeystroke(treeFiles)
        actionRefresh.activateKeystroke(treeFiles)
        actionOpenExplorer.activateKeystroke(treeFiles)
        actionOpenSystem.activateKeystroke(treeFiles)

        addAction(actionGoUp)

        val p: JPanel = contentPane as JPanel

        p.registerKeyboardAction(actionOpenFile, actionGoInto, actionGoUp,
                actionExpandSubTree, actionRefresh, actionOpenExplorer, actionOpenSystem)


        val renderer = object : DefaultTreeCellRenderer() {
            override fun getTreeCellRendererComponent(tree: JTree?, value: Any?, sel: Boolean, expanded: Boolean, leaf: Boolean, row: Int, hasFocus: Boolean): Component {
                val f = value as FolderTreeNode


                return super.getTreeCellRendererComponent(tree, f.file.name, sel, expanded, leaf, row, hasFocus)
            }
        }
        renderer.leafIcon = IconFontSwing.buildIcon(FontAwesomeRegular.FILE_CODE, 12f)
        renderer.openIcon = IconFontSwing.buildIcon(FontAwesomeRegular.FOLDER_OPEN, 12f)
        renderer.closedIcon = IconFontSwing.buildIcon(FontAwesomeRegular.FOLDER, 12f)
        treeFiles.cellRenderer = renderer

        ///val button = JPanel(MigLayout("fillX", "[pref][fill][pref]"))
        val button = JPanel(BorderLayout(2, 2))
        val lbl = JLabel("Root:")
        val btn = JButton()
        button.add(lbl, BorderLayout.WEST)
        button.add(txtFolder, BorderLayout.CENTER)
        button.add(btn, BorderLayout.EAST)

        btn.addActionListener {
            val fileChooser = JFileChooser((treeFiles.model.root as FolderTreeNode).file)
            fileChooser.fileSelectionMode = JFileChooser.DIRECTORIES_ONLY
            fileChooser.isAcceptAllFileFilterUsed = false

            when (fileChooser.showOpenDialog(this.contentPane)) {
                JFileChooser.APPROVE_OPTION -> {
                    treeFiles.model = DefaultTreeModel(FolderTreeNode(fileChooser.selectedFile, this::fileFilter))
                    txtFolder.text = fileChooser.selectedFile.absolutePath
                }
            }
        }

        txtFolder.addActionListener {
            val file = File(txtFolder.text)
            if (file.exists())
                treeFiles.model = DefaultTreeModel(FolderTreeNode(file, this::fileFilter))
        }

        add(button, BorderLayout.NORTH)
        add(JScrollPane(treeFiles))
    }

    val suffixes by lazy {
        lookup.get<EditorFactory>().getSupportedSuffixes()
    }

    private fun fileFilter(file: File): Boolean {
        return true
        //if (file.isDirectory) return true
        //return file.extension in suffixes
    }
}

fun JComponent.registerKeyboardAction(vararg actions: IdeAction, modifier: Int = JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT) {
    actions.forEach { action ->
        registerKeyboardAction(action, action.accelerator, modifier)
    }
}


data class FolderTreeNode(val file: File, val filter: (File) -> Boolean) : TreeNode {
    var children: List<FolderTreeNode> = arrayListOf()
        get() {
            val cmpFile = compareBy<File> { it.name }
            val cmpDirectory = compareBy<File> { it.isDirectory }.reversed()
            val cmp = cmpDirectory.thenComparing(cmpDirectory)

            if (field.isEmpty())
                field = file.listFiles()
                        ?.filter(filter)
                        ?.sortedWith(cmp)
                        ?.map { FolderTreeNode(it, filter) }
                        ?: listOf()
            return field
        }

    override fun children(): Enumeration<out TreeNode> = Collections.enumeration(children)
    override fun isLeaf(): Boolean = !file.isDirectory
    override fun getChildCount(): Int = children.size
    override fun getParent(): TreeNode = FolderTreeNode(file.parentFile, filter)
    override fun getChildAt(childIndex: Int): TreeNode = children[childIndex]
    override fun getIndex(node: TreeNode?): Int = children.indexOf(node)
    override fun getAllowsChildren(): Boolean = isLeaf
}


fun JTree.expandSubTree(it: TreePath) {
    this.expandPath(it)
    val last = it.lastPathComponent
    val childCount = getModel().getChildCount(last)
    for (idx in 0 until childCount) {
        val np = it.pathByAddingChild(getModel().getChild(last, idx))
        expandSubTree(np)
    }
}

