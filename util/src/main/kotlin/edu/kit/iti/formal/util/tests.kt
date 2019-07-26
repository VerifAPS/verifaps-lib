package edu.kit.iti.formal.util

import java.io.File

val isWindows by lazy {
    System.getProperty("os.name") == "WINDOWS"
}

fun findProgram(program: String): File? {
    val file = File(program)
    return if (file.exists())
        file
    else
        findProgramInPath(program)
}

fun findProgramInPath(program: String): File? {
    val path = System.getenv("PATH")
    val folders = path.split(if (isWindows) ";" else ":")
    folders.forEach {
        val cand = File(it, program)
        if (cand.exists()) {
            return cand
        }
    }
    return null
}
