package edu.kit.iti.formal.stvs.logic.io

import java.io.File
import java.nio.file.Paths
import kotlin.io.path.exists

/**
 * Created by csicar on 20.07.17.
 */
object ExecutableLocator {
    fun findExecutableFile(executableName: String): File? {
        val envPath = System.getenv("PATH")
        if (envPath.isEmpty()) {
            return null
        }
        return envPath.split(":".toRegex()).asSequence()
            .filter { it.isNotBlank() }
            .map { Paths.get(it, executableName) }
            .filter { it.exists() }
            .firstOrNull()?.toFile()
    }

    fun findExecutableFileAsString(executableName: String): String? {
        return findExecutableFile(executableName)?.toString()
    }
}
