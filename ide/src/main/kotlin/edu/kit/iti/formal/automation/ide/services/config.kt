package edu.kit.iti.formal.automation.ide.services

import edu.kit.iti.formal.automation.ide.IDE_LOGGER
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*
import kotlin.reflect.KProperty

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.05.19)
 */
class ConfigurationPaths {
    val operationSystem by lazy {
        val os = System.getProperty("os.name");
        when {
            os.contains("Mac") -> "mac"
            os.contains("Windows") -> "win"
            os.contains("Linux") -> "lin"
            else -> ""
        }
    }

    val applicationName = "verifaps-ide"

    val configFolder by lazy {
        val os = System.getProperty("os.name");
        val home = System.getProperty("user.home");
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
        IDE_LOGGER.info("Configuration folder: $p")
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


abstract class Configuration(val properties: Properties = Properties(), val prefix: String = "") {
    protected fun integer(default: Int = 0) = PropertiesProperty(default, { it.toIntOrNull() })
    protected fun string(default: String = "") = PropertiesProperty<String>(default, { it })
    protected fun boolean(default: Boolean) = PropertiesProperty(default, { it.equals("true", true) })

    fun save(path: Path) {
        properties.store(path.bufferedWriter(), "")
    }

    fun load(path: Path) {
        properties.load(path.bufferedReader())
    }

}

class ApplicationConfiguration() : Configuration() {
    var posX by integer(10)
    var posY by integer(10)
    var windowHeight by integer(400)
    var windowWidth by integer(600)
    var maximized by boolean(false)
}

