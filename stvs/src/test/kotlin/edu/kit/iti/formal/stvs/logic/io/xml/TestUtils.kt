/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.StvsApplication
import java.io.ByteArrayOutputStream
import java.io.File
import java.io.OutputStream
import java.net.URISyntaxException
import java.nio.file.Paths
import kotlin.io.path.bufferedReader

/**
 * @author Benjamin Alt
 */
object TestUtils {
    private val prefixes =
        hashMapOf(
            FileType.SESSION to "session",
            FileType.CONCRETE to "concrete_spec",
            FileType.CONSTRAINT to "constraint_spec",
            FileType.CONFIG to "config",
        )

    private val statuses: HashMap<Status, Regex> = hashMapOf(
        Status.VALID to "(?!.*invalid.*).*valid.*".toRegex(),
        Status.ALL to ".*".toRegex(),
    )

    fun removeWhitespace(input: String) = input.replace("[\t\n\r ]+".toRegex(), "").replace("\r\n", "\n").trim()

    fun getResource(name: String) = javaClass.getResourceAsStream(name) ?: error("Could not find resource file: $name")

    @Throws(URISyntaxException::class)
    fun getTestFiles(type: FileType, status: Status): List<File> {
        val res: MutableList<File> = ArrayList()
        for (testSet in testSets) {
            val children = testSet.list()
            if (children != null) {
                for (childName in children) {
                    if (childName.startsWith(prefixes[type]!!) &&
                        statuses[status]!!.matches(childName)
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
                StvsApplication::class.java.getResource("testSets")!!.toURI(),
            )
            val res: MutableList<File> = ArrayList()
            for (childName in testSetsDirectory.list()!!) {
                res.add(File(testSetsDirectory.absolutePath + File.separator + childName))
            }
            return res
        }

    fun readFromFile(path: String) = Paths.get(path).bufferedReader().readText()

    fun stringOutputStream(block: (OutputStream) -> Unit): String {
        val out = ByteArrayOutputStream(4096)
        block(out)
        return out.toString("utf-8")
    }

    enum class FileType {
        SESSION,
        CONCRETE,
        CONSTRAINT,
        CONFIG,
    }

    enum class Status {
        VALID,
        ALL,
    }
}