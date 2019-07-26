package edu.kit.iti.formal.automation.ide.services

import edu.kit.iti.formal.automation.ide.Lookup
import java.io.File
import java.nio.file.Files
import java.nio.file.Path
import java.util.function.Consumer

typealias RecentFilesUpdateListener = Consumer<List<File>>

interface RecentFilesService {
    val defaultFile: Path
    val recentFiles: List<File>

    fun save(file: Path = defaultFile)
    fun load(file: Path = defaultFile)
    fun add(f: File)
    fun clear()

    fun addListener(l: RecentFilesUpdateListener)
    fun removeListener(l: RecentFilesUpdateListener)

    operator fun contains(f: File): Boolean
}

class RecentFilesImpl(lookup: Lookup) : RecentFilesService {
    protected var listenerList = arrayListOf<RecentFilesUpdateListener>()

    override val recentFiles = arrayListOf<File>()
    override val defaultFile = lookup.get<ConfigurationPaths>().recentFiles

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

    override fun load(file: Path) {
        if (defaultFile.exists()) {
            defaultFile.useLines {
                it.forEach { add(File(it)) }
            }
        }
    }

    override fun save(file: Path) {
        file.bufferedWriter().use { w ->
            recentFiles.forEach {
                w.write("${it.absolutePath}\n")
            }
        }
    }

    override fun clear() =
            recentFiles.clear()
}

fun <T> Path.useLines(block: (Sequence<String>) -> T): T = bufferedReader().useLines(block)
fun Path.exists(): Boolean = Files.exists(this)
fun Path.bufferedWriter() = Files.newBufferedWriter(this)
fun Path.bufferedReader() = Files.newBufferedReader(this)
