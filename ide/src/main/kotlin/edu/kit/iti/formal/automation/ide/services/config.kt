package edu.kit.iti.formal.automation.ide.services

import edu.kit.iti.formal.automation.ide.FontAwesomeRegular
import edu.kit.iti.formal.automation.ide.FontAwesomeSolid
import edu.kit.iti.formal.automation.ide.FontIcon
import edu.kit.iti.formal.util.info
import java.io.File
import java.net.URL
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*
import javax.swing.ImageIcon
import javax.swing.KeyStroke
import kotlin.reflect.KProperty

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.05.19)
 */
object ConfigurationPaths {
    val operationSystem by lazy {
        val os = System.getProperty("os.name")
        when {
            os.contains("Mac") -> "mac"
            os.contains("Windows") -> "win"
            os.contains("Linux") -> "lin"
            else -> ""
        }
    }

    val applicationName = "verifaps-ide"

    val configFolder by lazy {
        val home = System.getProperty("user.home")
        val p = when (operationSystem) {
            "mac" -> Paths.get(home, "Library", "Application Support", applicationName)
            "win" -> {
                val version = System.getProperty("os.version")
                Paths.get(System.getenv("APPDATA"), applicationName)
            }
            "lin" -> {
                Paths.get(home, ".config", applicationName)
            }
            else -> Paths.get(applicationName)
        }
        Files.createDirectories(p)
        info("Configuration folder: $p")
        p
    }


    val layoutFile by lazy {
        configFolder.resolve("layout.data")
    }

    val configuration by lazy {
        configFolder.resolve("config.properties")
    }

    val recentFiles by lazy {
        configFolder.resolve("recentfiles")
    }
}

class PropertiesProperty<T>(
        val default: T,
        val read: (String) -> T?,
        val write: (T) -> String = { it.toString() }) {
    operator fun getValue(config: Configuration, prop: KProperty<*>): T =
            config.properties.getProperty(config.prefix + prop.name)?.let(read) ?: default

    operator fun setValue(config: Configuration, prop: KProperty<*>, v: T) {
        config.properties.setProperty(config.prefix + prop.name, write(v))
    }
}


abstract class Configuration(val properties: Properties = Properties(),
                             val prefix: String = "") {
    protected fun integer(default: Int = 0) = PropertiesProperty(default, { it.toIntOrNull() })
    protected fun string(default: String = "") = PropertiesProperty<String>(default, { it })
    protected fun boolean(default: Boolean) = PropertiesProperty(default, { it.equals("true", true) })

    fun save(path: Path) {
        properties.store(path.bufferedWriter(), "")
    }

    fun load(path: Path) {
        if (path.exists())
            properties.load(path.bufferedReader())
    }

    fun load(resource: URL?) {
        resource?.openStream()?.use {
            properties.load(it)
        }
    }

    fun write(configuration: Path) {
        configuration.bufferedWriter().use {
            properties.store(it, "automatically saved, do not change.")
        }
    }
}

object ApplicationConfiguration : Configuration() {
    var posX by integer(10)
    var posY by integer(10)
    var windowHeight by integer(400)
    var windowWidth by integer(600)
    var maximized by boolean(false)
    var lastNavigatorPath by string(File(".").absolutePath)
}

object UserConfiguration : Configuration() {
    init {
        load(javaClass.getResource("/ide.properties"))
        load(Paths.get(System.getenv()["user.home"], ".verifaps-ide.properties"))
        load(Paths.get("verifaps-ide.properties"))
    }

    val verbose: Boolean by boolean(false)

    fun getActionMenuPath(actionName: String) =
            getValue("$actionName.menu") ?: ""

    private fun getValue(s: String): String? {
        val v = properties[s]?.toString()
        if (v.isNullOrBlank()) return null
        return v
    }

    fun getActionKeyStroke(actionName: String) = getValue("$actionName.key")?.let { KeyStroke.getKeyStroke(it) }
    fun getActionPrio(actionName: String): Int = getValue("$actionName.priority")?.toInt() ?: 0
    fun getActionShortDesc(actionName: String) = getValue("$actionName.shortdesc") ?: ""
    fun getActionLongDesc(actionName: String) = getValue("$actionName.longdesc") ?: ""

    fun getActionSmallIcon(actionName: String) = getValue("$actionName.smallIcon")?.let { ImageIcon(it) }
    fun getActionLargeIcon(actionName: String) = getValue("$actionName.largeIcon")?.let { ImageIcon(it) }
    fun getActionFontIcon(actionName: String): FontIcon? = getValue("$actionName.fontIcon")?.let {
        try {
            return FontAwesomeRegular.valueOf(it)
        } catch (e: IllegalArgumentException) {
            try {
                return FontAwesomeSolid.valueOf(it)
            } catch (e: IllegalArgumentException) {
                error(e.message!!)
            }
        }
    }

    fun getActionText(actionName: String): String = getValue("$actionName.text") ?: "$actionName.text n/a"
}