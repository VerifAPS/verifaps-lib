package edu.kit.iti.formal.automation.ide

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import javafx.application.Application
import javafx.geometry.Orientation
import javafx.scene.Node
import javafx.scene.Scene
import javafx.scene.control.*
import javafx.scene.layout.BorderPane
import javafx.scene.layout.HBox
import javafx.scene.layout.VBox
import javafx.scene.text.Font
import javafx.stage.Stage
import org.antlr.v4.runtime.CharStreams
import org.fxmisc.richtext.CodeArea
import org.fxmisc.richtext.LineNumberFactory
import org.fxmisc.richtext.model.StyleSpans
import org.fxmisc.richtext.model.StyleSpansBuilder
import java.io.File
import java.util.*


fun main(args: Array<String>) {
    Application.launch(IdeFx::class.java, *args)
}

class IdeFx : Application() {

    override fun start(primaryStage: Stage) {
        val main = MainScene()
        primaryStage.scene = main.scene
        primaryStage.title = "VERIFAPS IDE"
        primaryStage.show()
    }

    override fun stop() {
        super.stop()
    }
}

class MainScene {
    val root = BorderPane()
    val scene = Scene(root, 300.0, 300.0)
    val menu = IdeMenu()
    val fileNavigator = FileNavigator()
    val outline = FileOutline()

    val left = SplitPane()
    val center = TabPane()

    init {
        root.top = menu.ui
        left.items.setAll(outline.ui, fileNavigator.ui)
        left.orientation = Orientation.VERTICAL
        root.center = SplitPane(left, center)


        val content = CodeArea("")
        content.paragraphGraphicFactory = LineNumberFactory.get(content) { String.format("%03d", it) }
        content.textProperty().addListener { obs, oldText, newText -> content.setStyleSpans(0, computeHighlighting(newText)) }
        content.isLineHighlighterOn = true
        center.tabs.add(Tab("Test", content))
    }
}

private fun computeHighlighting(text: String): StyleSpans<Collection<String>>? {
    val spansBuilder = StyleSpansBuilder<Collection<String>>()
    val lexer = IEC61131Lexer(CharStreams.fromString(text))
    do {
        val tok = lexer.nextToken()
        if(tok.type == -1) break
        val typ = lexer.vocabulary.getSymbolicName(tok.type)
        spansBuilder.add(Collections.singleton(typ), tok.text.length);
    } while (tok.type != -1)
    return spansBuilder.create()
}


class IdeMenu {
    val file = Menu("File")
    val edit = Menu("Edit")
    val view = Menu("View")
    val tools = Menu("Tools")
    val ui = MenuBar(file, edit, view, tools)
}

abstract class TitledPanel(header: String) {
    val ui
        get() = root
    val root = BorderPane()
    val buttonBox = HBox()
    abstract val main: Node

    init {
        root.top = VBox(createHeaderLabel(header), buttonBox, Separator())
        root.center = main
    }
}

class FileNavigator : TitledPanel("Navigator") {
    val treeFile = TreeView<File>()
    override val main: Node
        get() = treeFile

    init {

    }
}


private fun createHeaderLabel(text: String) = Label(text).also {
    it.font = Font(it.font.name, it.font.size + 6)
}

class FileOutline : TitledPanel("Outline") {
    val outlineTree = TreeView<Any>()

    init {
    }

    override val main: Node
        get() {
            return outlineTree
        }
}
