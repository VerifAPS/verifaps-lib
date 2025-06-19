package edu.kit.iti.formal.automation.fx

import javafx.beans.property.SimpleObjectProperty
import javafx.collections.FXCollections
import javafx.collections.ObservableList
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.Node
import javafx.scene.control.*
import javafx.scene.control.cell.TextFieldTreeCell
import javafx.scene.input.KeyCombination
import javafx.scene.paint.Color.*
import javafx.util.StringConverter
import org.kordamp.ikonli.fontawesome5.FontAwesomeSolid
import org.kordamp.ikonli.javafx.FontIcon
import tornadofx.View
import tornadofx.contextmenu
import tornadofx.separator
import java.awt.Desktop
import java.io.IOException
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import kotlin.io.path.extension
import kotlin.io.path.isDirectory
import kotlin.io.path.name
import tornadofx.item as titem

/**
 *
 * @author Alexander Weigl
 * @version 1 (3/21/21)
 */

class FileNavigator(main: IdeView) : View("Navigator") {
    val rootFile = SimpleObjectProperty(
        this, "rootFile",
        Paths.get(".").normalize().toAbsolutePath()
    )
    val treeFile = TreeView(SimpleFileTreeItem(rootFile.value))
    override val root = treeFile

    private fun markFolderUnderMouse(event: ActionEvent) {

    }


    val contextMenu: ContextMenu = contextmenu {
        item("Open file", "ENTER", null) {
            markFolderUnderMouse(it)
            treeFile.selectionModel.selectedItem?.let {
                main.open(it.value.toFile())
            }
        }

        item("Open in explorer") {
            markFolderUnderMouse(it)
            (treeFile.selectionModel.selectedItem)?.let { file ->
                try {
                    Desktop.getDesktop()?.browseFileDirectory(file.value.toFile())
                } catch (e: UnsupportedOperationException) {
                    ProcessBuilder("explorer", "/select,${file.value}").start()
                }
            }
        }
        item("System open") {
            markFolderUnderMouse(it)
            (treeFile.selectionModel.selectedItem)?.let { file ->
                try {
                    Desktop.getDesktop()?.open(file.value.toFile())
                } catch (e: UnsupportedOperationException) {
                    ProcessBuilder("explorer", "/select,${file.value}").start()
                }
            }
        }

        separator()

        item("tree-new-file") {
            markFolderUnderMouse(it)
            treeFile.selectionModel.selectedItem?.let { item ->
                val path = item.value!!
                val dialog = TextInputDialog()
                dialog.contentText = "File name:"
                val name = dialog.showAndWait()
                name.ifPresent {
                    val newFile = path.resolve(it)
                    try {
                        Files.createFile(newFile)
                        main.open(newFile.toFile())
                        refresh()
                    } catch (e: IOException) {
                        val a = Alert(Alert.AlertType.ERROR)
                        a.contentText = e.message
                        a.show()
                    }
                }
            }
        }
        item("tree-new-directory") {
            markFolderUnderMouse(it)
            treeFile.selectionModel.selectedItem?.let { item ->
                val path = item.value!!
                val dialog = TextInputDialog()
                dialog.contentText = "Folder name:"
                val name = dialog.showAndWait()
                name.ifPresent {
                    val newFile = path.resolve(it)
                    try {
                        Files.createDirectory(newFile)
                        main.open(newFile.toFile())
                        refresh()
                    } catch (e: IOException) {
                        val a = Alert(Alert.AlertType.ERROR)
                        a.contentText = e.message
                        a.show()
                    }
                }
            }
        }
        separator()


        item("Refresh") {}

        item("Expand Tree") {
            markFolderUnderMouse(it)
        }

        separator()

        item("Go up") {
            markFolderUnderMouse(it)
            treeFile.root.value?.let { file ->
                treeFile.root = SimpleFileTreeItem(file.parent.toAbsolutePath())
                treeFile.root.isExpanded = true
            }
        }
        item("Go into") {
            markFolderUnderMouse(it)
            (treeFile.selectionModel.selectedItem)?.let { file ->
                treeFile.root = SimpleFileTreeItem(file.value.toAbsolutePath())
                treeFile.root.isExpanded = true
            }
        }

        separator()

        item("Rename file") { }
        item("Delete file") {}

        separator()
    }

    fun refresh(): Unit {

    }

    init {
        treeFile.contextMenu = contextMenu
        treeFile.isEditable = false
        treeFile.isShowRoot = true
        rootFile.addListener { _, _, new ->
            treeFile.root = SimpleFileTreeItem(new)
        }
        treeFile.setCellFactory { tv ->
            TextFieldTreeCell(object : StringConverter<Path>() {
                override fun toString(obj: Path?): String = obj?.fileName.toString() ?: ""
                override fun fromString(string: String?): Path = Paths.get(string)
            })
        }
        treeFile.root.isExpanded = true
    }
}

fun ContextMenu.item(name: String, key: String? = null, ikon: String? = null, event: (ActionEvent) -> Unit) {
    val icon = ikon?.let { ref -> FontIcon(ref) }
    titem(name, key?.let { KeyCombination.keyCombination(it) }, icon) {
        onAction = EventHandler(event)
    }
}

class SimpleFileTreeItem(f: Path) : TreeItem<Path>(f) {
    private val pathComparator: Comparator<TreeItem<Path>> = java.util.Comparator.comparingInt<TreeItem<Path>> {
        if (Files.isDirectory(it.value)) 0 else 1
    }.thenComparing { it -> it.value.name }

    private var isFirstTimeChildren = true
    private var isFirstTimeLeaf = true
    private var isLeaf = false

    init {
        graphic = NavigationIconFinder.find(f)
    }

    override fun getChildren(): ObservableList<TreeItem<Path>> {
        if (isFirstTimeChildren) {
            isFirstTimeChildren = false
            super.getChildren().setAll(buildChildren(this))
        }
        return super.getChildren()
    }

    override fun isLeaf(): Boolean {
        if (isFirstTimeLeaf) {
            isFirstTimeLeaf = false
            val f = value as Path
            isLeaf = Files.isRegularFile(f)
        }
        return isLeaf
    }

    private fun buildChildren(node: TreeItem<Path>): ObservableList<TreeItem<Path>> {
        val f = node.value
        if (f != null && Files.isDirectory(f)) {
            val children: ObservableList<TreeItem<Path>> = FXCollections.observableArrayList()
            Files.list(f).forEach {
                children.add(SimpleFileTreeItem(it))
            }
            return children.sorted(pathComparator)
        }
        return FXCollections.emptyObservableList()
    }
}

object NavigationIconFinder {
    private val DIRECTORY = FontAwesomeSolid.FOLDER
    private val FILE = FontAwesomeSolid.FILE
    private val FILE_CODE = FontAwesomeSolid.FILE_CODE

    private fun get(ref: String): FontIcon? {
        return FontIcon(ref)
    }

    fun find(p: Path): Node? {
        if (p.isDirectory()) {
            return FontIcon(DIRECTORY)
        }

        return when (p.extension) {
            "gtt", "rtt", "st" -> FontIcon(FILE_CODE)
            else -> FontIcon(FILE).also {
                it.iconColor = LIGHTGREY
            }
        }
    }
}
