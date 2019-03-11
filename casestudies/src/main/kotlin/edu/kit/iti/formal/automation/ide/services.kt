package edu.kit.iti.formal.automation.ide

import java.awt.Color
import java.io.File
import java.util.function.Consumer
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

interface GetFileChooser {
    val fileChooser: JFileChooser
}

class Colors {
    val BLUE = Color(74, 72, 133)
    val LIGHT_BLUE = Color(148, 198, 206)
    val VIOLET = Color(175, 137, 193)
    val DARK_VIOLET = Color(107, 8, 114)
    val DARK_GREEN = Color(2, 113, 129)
    val BACKGROUND = Color(200, 200, 200)
    val HIGHTLIGHT_LINE = Color(255, 255, 255)
    val GREY = Color(109, 109, 109)
}

typealias RecentFilesUpdateListener = Consumer<List<File>>

interface RecentFiles {
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

class RecentFilesImpl : RecentFiles {
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

class Lookup(var parent: Lookup? = null) {
    private val serviceMap = hashMapOf<Class<*>, Any>()

    fun <T> get(service: Class<T>): T {
        val t = serviceMap[service]
        return if (t == null) {
            if (parent != null) parent!!.get(service)
            else throw IllegalStateException("Service $service not registered")
        } else {
            t as T
        }
    }

    inline fun <reified T> get() = get(T::class.java)

    fun <T> register(obj: T, service: Class<T>) {
        serviceMap.put(service, obj!!)
    }

    inline fun <reified T> register(obj: T) = register<T>(obj, T::class.java)

    inline fun <reified T> with(): ReadWriteProperty<Any, T> {
        return object : ReadWriteProperty<Any, T> {
            override fun getValue(thisRef: Any, property: KProperty<*>): T = get()
            override fun setValue(thisRef: Any, property: KProperty<*>, value: T) = register(value)
        }
    }
}
