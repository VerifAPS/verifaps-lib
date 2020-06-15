package edu.kit.iti.formal.automation.ide

import edu.kit.iti.formal.automation.st.ast.Position
import org.fife.ui.rsyntaxtextarea.Style
import java.awt.Color
import java.awt.Font
import java.io.File
import java.util.*
import javax.swing.Icon
import javax.swing.JFileChooser
import kotlin.properties.ReadWriteProperty
import kotlin.reflect.KProperty


/**
 *
 * @author Alexander Weigl
 * @version 1 (11.03.19)
 */
//Services
interface Messager {
    fun display(msg: String, icon: Icon? = null)
}

interface JumpService {
    fun jumpTo(editor: CodeEditor, position: Position? = null)
    fun jumpTo(position: Position)
    fun selectInEditor(name: String, start: Int, stop: Int?)
    fun changeInEditor(editorName: String, start: Int, stop: Int, newText: String)
}

interface FileOpen {
    fun open(file: File)
}

interface GetFileChooser {
    val fileChooser: JFileChooser
}

interface ActionService {
    fun registerAction(act: IdeAction)
    fun deregisterAction(act: IdeAction)
}

interface TabManagement {
    fun addToolTab(pane: ToolPane)
    fun addEditorTab(pane: CodeEditor)
}

interface EditingDialogs {
    fun openReplaceDialog(codeEditor: CodeEditor)
    fun openSearchDialog(codeEditor: CodeEditor)
}

interface StatusService {
    fun publishMessage(status: String)
}


abstract class Colors {
    var defaultFont = Font(Font.MONOSPACED, 0, 14)
    abstract val background: Color
    abstract val separators: Style
    abstract val control: Style
    abstract val structural: Style
    abstract val identifier: Style
    abstract val operators: Style
    abstract val literal: Style
    abstract val comment: Style
    abstract val default: Style
    abstract val error: Style
    abstract val types: Style
    abstract val highLightLine: Color

    companion object {
        protected fun hsl(h: Int, s: Int, l: Int): Color = Color.getHSBColor(h / 360f, s / 100f, l / 100f)
    }

    fun style(init: Style.() -> Unit): Style {
        val style = Style()
        style.font = defaultFont
        style.foreground = Color.BLACK
        init(style)
        return style
    }
}

//https://atelierbram.github.io/syntax-highlighting/atelier-schemes/dune/
object DuneColors : Colors() {
    val base00 = Color.decode("#20201d")
    val base01 = Color.decode("#292824")
    val base02 = Color.decode("#6e6b5e")
    val base03 = Color.decode("#7d7a68")
    val base04 = Color.decode("#999580")
    val base05 = Color.decode("#a6a28c")
    val base06 = Color.decode("#e8e4cf")
    val base07 = Color.decode("#fefbec")
    val base08 = Color.decode("#d73737")
    val base09 = Color.decode("#b65611")
    val base0a = Color.decode("#ae9513")
    val base0b = Color.decode("#60ac39")
    val base0c = Color.decode("#1fad83")
    val base0d = Color.decode("#6684e1")
    val base0e = Color.decode("#b854d4")
    val base0f = Color.decode("#d43552")

    val red = base08
    val orange = base09
    val yellow = base0a
    val green = base0b
    val cyan = base0c
    val blue = base0d
    val violet = base0e
    val magenta = base0f

    private fun hsl(h: Int, s: Int, l: Int): Color = Color.getHSBColor(h / 360f, s / 100f, l / 100f)

    override val background = base07

    override val separators = style { foreground = cyan }

    override val control = style { foreground = violet }

    override val structural = style { foreground = orange }

    override val identifier = style { foreground = red }

    override val operators: Style = style { foreground = magenta }

    override val literal = style { foreground = green }

    override val comment = style { foreground = base05 }

    override val default = style {}

    override val error = style {
        foreground = red
        underline = true
    }

    override val types = style { foreground = blue }
    override val highLightLine: Color = base06

    val BLUE = Color(74, 72, 133)
    val LIGHT_BLUE = Color(148, 198, 206)
    val VIOLET = Color(175, 137, 193)
    val DARK_VIOLET = Color(107, 8, 114)
    val DARK_GREEN = Color(2, 113, 129)
    val BACKGROUND = Color(200, 200, 200)
    val GREY = Color(109, 109, 109)
}

class Lookup {
    private val serviceMap = hashMapOf<Class<*>, LinkedList<Any>>()
    private val serviceListener = hashMapOf<Class<*>, MutableList<() -> Unit>>()
    private val allListener: MutableList<() -> Unit> = LinkedList()

    private fun <T> getList(service: Class<T>): MutableList<T> = serviceMap.computeIfAbsent(service) { LinkedList<Any>() } as MutableList<T>

    fun <T> get(service: Class<T>): T {
        val t = getList(service)
        return if (t.isEmpty()) {
            throw IllegalStateException("Service $service not registered")
        } else {
            t.first()
        }
    }

    inline fun <reified T> get() = get(T::class.java)

    fun <T> register(obj: T, service: Class<T>) {
        getList(service).add(0, obj!!)
        firePropertyChange(service)
    }

    inline fun <reified T> register(obj: T) = register(obj, T::class.java)

    fun <T> deregister(obj: T, service: Class<T>) {
        val b = getList(service).remove(obj)
        if (b) firePropertyChange(service)
    }

    inline fun <reified T> deregister(obj: T) = deregister(obj, T::class.java)

    fun <T> getAll(service: Class<T>) = getList(service).toList()
    inline fun <reified T> getAll() = getAll(T::class.java)

    fun <T : Any> getAllSubtypes(service: Class<T>): Sequence<T> {
        val seq = emptySequence<T>()
        val s = serviceMap.values
                .asSequence()
                .flatMap { it.asSequence() }
                .mapNotNull { it as? T }
        return s + seq
    }

    inline fun <reified T> with(): ReadWriteProperty<Any, T> {
        return object : ReadWriteProperty<Any, T> {
            override fun getValue(thisRef: Any, property: KProperty<*>): T = get()
            override fun setValue(thisRef: Any, property: KProperty<*>, value: T) = register(value)
        }
    }


    fun <T> getListeners(name: Class<T>) = serviceListener.computeIfAbsent(name) { LinkedList() }
    fun addChangeListener(listener: () -> Unit) = allListener.add(listener)
    fun <T> addChangeListener(name: Class<T>, listener: () -> Unit) = getListeners(name).add(listener)
    fun <T> removeChangeListener(name: Class<T>, listener: () -> Unit) = getListeners(name).remove(listener)
    fun removeChangeListener(listener: () -> Unit) = allListener.remove(listener)

    fun firePropertyChange(name: Class<*>) {
        getListeners(name).forEach { it() }
        allListener.forEach { it() }
    }

    fun firePropertyChange() {
        serviceListener.keys.forEach { getListeners(it).forEach { it() } }
        allListener.forEach { it() }
    }


    private class ALL
}
