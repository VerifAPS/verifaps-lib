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
import java.io.File
import java.io.IOException
import java.net.URISyntaxException
import java.nio.file.FileSystems
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*
import java.util.stream.Collectors

/**
 *
 * @author Alexander Weigl
 * @version 1 (13.02.19)
 */
object LoadHelp {
    /*
    fun getResources(folder: String): Array<File> {
        val f = LoadHelp::class.java.classLoader.getResource(folder)
        if (f == null) {
            System.err.format("Could not find %s%n", folder)
            return arrayOf()
        }
        if()
        println("Found folder: ${f.file}")
        val file = File(f.file)
        return file.listFiles() ?: arrayOf()
    }*/

    /**
     * List directory contents for a resource folder. Not recursive.
     * This is basically a brute-force implementation.
     * Works for regular files and also JARs.
     *
     * @author Greg Briggs
     * @param clazz Any java class that lives in the same place as the resources you want.
     * @param path Should end with "/", but not start with one.
     * @return Just the name of each member item, not the full paths.
     * @throws URISyntaxException
     * @throws IOException
     */
    @JvmStatic
    @Throws(URISyntaxException::class, IOException::class)
    fun getResources(path: String, clazz: Class<*> = LoadHelp::class.java): List<Path> {
        var dirURL = clazz.classLoader.getResource(path)
        if (dirURL != null && dirURL.protocol.equals("file")) {
            /* A file path: easy enough */
            println("Found folder: ${dirURL.file}")
            return File(dirURL.toURI()).listFiles().map { it.toPath() }
        }

        if (dirURL === null) {
            /*
             * In case of a jar file, we can't actually find a directory.
             * Have to assume the same jar as clazz.
             */
            val me = clazz.name.replace(".", "/") + ".class"
            dirURL = clazz.classLoader.getResource(me)
        }

        if (dirURL!!.protocol.equals("jar")) {
            /* A JAR path */
            // strip out only the JAR file
            var jarPath = dirURL.path.substring(5, dirURL.path.indexOf("!"))
            if (jarPath.startsWith("/C:")) {
                jarPath = jarPath.substring(1)
            }
            val fs = FileSystems.newFileSystem(Paths.get(jarPath), javaClass.classLoader)
            val dir = fs.getPath(path)
            return Files.list(dir).collect(Collectors.toList())
        }
        throw UnsupportedOperationException("Cannot list files for URL $dirURL")
    }

    fun getResource(path: String, clazz: Class<*> = LoadHelp::class.java): Path? {
        val dirURL = clazz.classLoader.getResource(path)
        if (dirURL === null) return null

        if (dirURL.protocol.equals("file")) {
            return File(dirURL.toURI()).toPath()
        }

        if (dirURL.protocol.equals("jar")) {
            /* A JAR path */
            // strip out only the JAR file
            var jarPath = dirURL.path.substring(5, dirURL.path.indexOf("!"))
            if (jarPath.startsWith("/C:")) {
                jarPath = jarPath.substring(1)
            }
            val fs = FileSystems.newFileSystem(Paths.get(jarPath), javaClass.classLoader)
            val dir = fs.getPath(path)
            return dir
        }
        throw UnsupportedOperationException("Cannot list files for URL $dirURL")
    }

    fun getPrograms() = getResources("edu/kit/iti/formal/automation/st/programs")
    fun getStatements() = getResources("edu/kit/iti/formal/automation/st/statements")
    fun getTypes() = getResources("edu/kit/iti/formal/automation/st/types")
}

/**
 * Created by weigl on 14.11.16.
 */
object TestUtils {
    @Throws(IOException::class)
    fun loadLines(filename: String): List<String> {
        val validExpression = ArrayList<String>(4096)
        val ve = TestUtils::class.java.getResourceAsStream(filename)

        if (ve == null) {
            System.err.println("Could not find: $filename")
            return validExpression
        }

        ve.bufferedReader().use { stream ->
            stream.forEachLine {
                if (!it.startsWith("#")) {
                    validExpression.add(it)
                }
            }
        }

        println("Found: " + filename + " with " + validExpression.size + " lines!")
        return validExpression
    }

    fun asParameters(cases: Array<String>): List<Array<Any>> = cases.map { arrayOf(it as Any) }
}
