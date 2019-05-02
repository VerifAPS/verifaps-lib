package edu.kit.iti.formal.automation.ide

import edu.kit.iti.formal.automation.st.ast.Position
import org.fife.ui.rsyntaxtextarea.Style
import java.awt.Color
import java.awt.Font
import java.io.File
import java.util.*
import java.util.function.Consumer
import javax.swing.Action
import javax.swing.Icon
import javax.swing.JFileChooser
import kotlin.collections.ArrayList
import kotlin.properties.ReadWriteProperty
import kotlin.reflect.KProperty
import org.fife.rsta.ui.search.ReplaceToolBar
import org.fife.rsta.ui.search.FindToolBar
import org.fife.rsta.ui.search.ReplaceDialog
import org.fife.rsta.ui.search.FindDialog


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
    fun jumpTo(editor: CodeEditor, position: Position)
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


//https://atelierbram.github.io/syntax-highlighting/atelier-schemes/dune/
object Colors {
    var defaultFont = Font(Font.MONOSPACED, 0, 12)

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

    private fun style(init: Style.() -> Unit): Style {
        val style = Style()
        style.font = defaultFont
        style.foreground = Color.BLACK
        init(style)
        return style
    }

    val background = base07

    val control = style { foreground = violet }

    val structural = style { foreground = violet }

    val identifier = style { foreground = red }

    val literal = style { foreground = green }

    val comment = style { foreground = base05 }

    val default = style {}

    val error = style {
        foreground = red
        underline = true
    }

    val types = style { foreground = blue }


    val BLUE = Color(74, 72, 133)
    val LIGHT_BLUE = Color(148, 198, 206)
    val VIOLET = Color(175, 137, 193)
    val DARK_VIOLET = Color(107, 8, 114)
    val DARK_GREEN = Color(2, 113, 129)
    val BACKGROUND = Color(200, 200, 200)
    val HIGHTLIGHT_LINE = base06
    val GREY = Color(109, 109, 109)
}

typealias RecentFilesUpdateListener = Consumer<List<File>>

interface RecentFilesService {
    val defaultFile: File
    val recentFiles: List<File>

    fun save(file: File = defaultFile)
    fun load(file: File = defaultFile)
    fun add(f: File)
    fun clear()

    fun addListener(l: RecentFilesUpdateListener)
    fun removeListener(l: RecentFilesUpdateListener)

    operator fun contains(f: File): Boolean
}

class RecentFilesImpl : RecentFilesService {
    protected var listenerList = arrayListOf<RecentFilesUpdateListener>()

    override val recentFiles = arrayListOf<File>()
    override val defaultFile = File(System.getenv("HOME"), ".iec61131ide-recentfiles")

    override fun add(f: File) {
        recentFiles += f
        fireListeners()
    }

    protected fun fireListeners() {
        listenerList.forEach { it.accept(recentFiles) }
    }

    override fun addListener(l: RecentFilesUpdateListener) {
        listenerList.add(l)
    }

    override fun removeListener(l: RecentFilesUpdateListener) {
        listenerList.remove(l)
    }

    override fun contains(f: File): Boolean = f in recentFiles

    init {
        load()
        Runtime.getRuntime().addShutdownHook(Thread { save() })
    }

    override fun load(file: File) {
        if (defaultFile.exists()) {
            defaultFile.useLines {
                it.forEach { add(File(it)) }
            }
        }
    }

    override fun save(file: File) {
        file.bufferedWriter().use { w ->
            recentFiles.forEach {
                w.write("${it.absolutePath}\n")
            }
        }
    }

    override fun clear() =
            recentFiles.clear()
}

class Lookup(val parent: Lookup? = null) {
    private val children = arrayListOf<Lookup>()
    private val serviceMap = hashMapOf<Class<*>, LinkedList<Any>>()

    init {
        parent?.children?.add(this)
    }

    private fun <T> getList(service: Class<T>): MutableList<T> = serviceMap.computeIfAbsent(service) { LinkedList<Any>() } as MutableList<T>

    fun <T> get(service: Class<T>): T {
        val t = getList(service)
        return if (t.isEmpty()) {
            if (parent != null) parent.get(service)
            else throw IllegalStateException("Service $service not registered")
        } else {
            t.first()
        }
    }

    inline fun <reified T> get() = get(T::class.java)
    fun <T> register(obj: T, service: Class<T>) {
        getList(service).add(0, obj!!)
        firePropertyChange(service)
    }

    fun <T> deregister(obj: T, service: Class<T>) {
        val b = getList(service).remove(obj)
        if (b) firePropertyChange(service)
        parent?.deregister(obj, service)
    }

    inline fun <reified T> deregister(obj: T) = deregister(obj, T::class.java)

    fun <T> getAll(service: Class<T>): List<T> {
        val t = ArrayList(getList(service))
        val p = parent?.getAll(service)
        if (p != null) t += p
        return t
    }

    fun <T : Any> getAllSubtypes(service: Class<T>): Sequence<T> {
        val seq = parent?.getAllSubtypes(service) ?: emptySequence()
        val s = serviceMap.values
                .asSequence()
                .flatMap { it.asSequence() }
                .mapNotNull { it as? T }
        return s + seq
    }


    inline fun <reified T> getAll() = getAll(T::class.java)

    inline fun <reified T> register(obj: T) = register(obj, T::class.java)

    inline fun <reified T> with(): ReadWriteProperty<Any, T> {
        return object : ReadWriteProperty<Any, T> {
            override fun getValue(thisRef: Any, property: KProperty<*>): T = get()
            override fun setValue(thisRef: Any, property: KProperty<*>, value: T) = register(value)
        }
    }

    fun dispose() {
        parent?.children?.remove(this)
    }

    val propertyListener = hashMapOf<Class<*>, MutableList<() -> Unit>>()
    fun <T> getListeners(name: Class<T>) = propertyListener.computeIfAbsent(name) { LinkedList() }
    fun addChangeListener(listener: () -> Unit) = addChangeListener(ALL::class.java, listener)
    fun <T> addChangeListener(name: Class<T>, listener: () -> Unit) = getListeners(name).add(listener)
    fun <T> removeChangeListener(name: Class<T>, listener: () -> Unit) = getListeners(name).remove(listener)
    fun removeChangeListener(listener: () -> Unit) = removeChangeListener(ALL::class.java, listener)
    fun firePropertyChange(name: Class<*>) {
        getListeners(name).forEach { it() }
        children.forEach { it.firePropertyChange(name) }
        getListeners(ALL::class.java).forEach { it() }
        children.forEach { it.firePropertyChange(ALL::class.java) }
    }

    private class ALL {}
}
