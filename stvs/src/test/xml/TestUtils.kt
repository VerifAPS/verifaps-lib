package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.StvsApplication

import java.io.File
import java.io.IOException
import java.net.URISyntaxException
import java.nio.file.Files
import java.nio.file.Paths
import java.util.*
import java.util.regex.Pattern
import kotlin.collections.ArrayList
import kotlin.collections.HashMap

/**
 * @author Benjamin Alt
 */
object TestUtils {
    private val prefixes: MutableMap<FileType, String>
    private val statuses: MutableMap<Status, Pattern>

    init {
        prefixes = EnumMap(FileType::class.java)
        prefixes[FileType.SESSION] =
            "session"
        prefixes[FileType.CONCRETE] =
            "concrete_spec"
        prefixes[FileType.CONSTRAINT] = "constraint_spec"
        prefixes[FileType.CONFIG] =
            "config"
        statuses = EnumMap(Status::class.java)
        statuses[Status.VALID] =
            Pattern.compile("(?!.*invalid.*).*valid.*")
        statuses[Status.ALL] = Pattern.compile(".*")
    }

    fun removeWhitespace(input: String?): String {
        return input!!.replace("\\s+".toRegex(), "")
    }

    @Throws(URISyntaxException::class)
    fun getTestFiles(type: FileType, status: Status): List<File> {
        val res: MutableList<File> = ArrayList()
        for (testSet in testSets) {
            val children = testSet.list()
            if (children != null) {
                for (childName in children) {
                    if (childName.startsWith(prefixes[type]!!) && statuses[status]!!
                            .matcher(childName)
                            .matches()
                    ) {
                        res.add(File(testSet.absolutePath + File.separator + childName))
                    }
                }
            }
        }
        return res
    }

    @get:Throws(URISyntaxException::class)
    private val testSets: List<File>
        get() {
            val testSetsDirectory = File(
                StvsApplication::class.java.getResource("testSets")!!.toURI()
            )
            val res: MutableList<File> = ArrayList()
            for (childName in testSetsDirectory.list()!!) {
                res.add(File(testSetsDirectory.absolutePath + File.separator + childName))
            }
            return res
        }

    @Throws(IOException::class)
    fun readFromFile(path: String?): String {
        return String(Files.readAllBytes(Paths.get(path)), charset("utf-8"))
    }

    @Throws(URISyntaxException::class)
    @JvmStatic
    fun main(args: Array<String>) {
        for (type in FileType.entries) {
            for (file in getTestFiles(type, Status.ALL)) {
                println(file.name)
            }
        }
    }

    enum class FileType {
        SESSION, CONCRETE, CONSTRAINT, CONFIG
    }

    enum class Status {
        VALID, ALL
    }
}
