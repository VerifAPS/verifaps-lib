package edu.kit.iti.formal.stvs.logic.io

import java.io.File
import java.util.*

/**
 * Created by csicar on 20.07.17.
 */
object ExecutableLocator {
    @JvmStatic
    fun findExecutableFile(executableName: String): Optional<File> {
        val envPath = System.getenv("PATH")
        if (envPath.isEmpty()) {
            return Optional.empty()
        }
        val path = Arrays.stream(envPath.split(":".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray())
            .map { pathname: String? -> File(pathname) }
            .filter { obj: File -> obj.exists() }
            .filter { file: File ->
                if (!file.isDirectory) {
                    return@filter false
                } else {
                    val files = file.listFiles { file1: File?, s: String -> s == executableName }
                    if (files == null) {
                        return@filter false
                    }
                    return@filter files.size != 0
                }
            }.findAny()
        return path.map { file: File? -> File(file, executableName) }
    }

    fun findExecutableFileAsString(executableName: String): Optional<String> {
        return findExecutableFile(executableName).map { obj: File -> obj.toString() }
    }
}
