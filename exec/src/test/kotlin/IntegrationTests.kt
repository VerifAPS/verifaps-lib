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
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test
import java.io.File
import java.nio.file.Paths
import kotlin.io.path.absolutePathString

val NUXMV_PATH by lazy {
    val file = File(System.getenv("HOME"), "share/nuXmv-2.1.0-linux64/bin/nuXmv")
    // val file = File(System.getenv("HOME"), "share/nuXmv-2.0.0-Linux/bin/nuXmv")
    if (file.exists()) {
        file.absolutePath
    } else {
        "nuXmv"
    }
}

val GETETA_PATH = Paths.get("build/install/exec/bin/geteta")
    .absolutePathString()
    .also {
        println("geteta path: $it")
    }

val RETETA_PATH = Paths.get("build/install/exec/bin/reteta")
    .absolutePathString()
    .also {
        println("reteta path: $it")
    }

class ProgramTester(vararg args: String) {
    var expectedErrorLevel = 0

    private var builder: ProcessBuilder = ProcessBuilder(*args)
        .directory(File("src/test/resources"))

    init {
        builder.environment().putIfAbsent("NUXMV", NUXMV_PATH)
    }

    fun check() {
        System.out.println("> Checking ${builder.command()} in ${builder.directory()}")
        var process = builder.start()
        process.waitFor()

        val exitCode = process.exitValue()
        val error = process.errorStream.bufferedReader().readText()
        val output = process.inputStream.bufferedReader().readText()

        System.err.println(error)
        println(output)

        Assertions.assertTrue(exitCode == expectedErrorLevel)
    }

    fun directory(dir: String) = also {
        val f = File(dir).absoluteFile
        Assertions.assertTrue(f.exists(), "File $f does not exist")
        builder.directory(f)
    }
}

fun getetaTester(vararg args: String) = ProgramTester(GETETA_PATH, *args)
fun retetaTester(vararg args: String) = ProgramTester(RETETA_PATH, *args)

class GetetaIntegrationTests {
    private fun geteta(vararg args: String) = getetaTester(*args).check()

    @Test
    fun help() = geteta("--help")

    @Test
    fun constantprogram() {
        getetaTester("-c", "constantprogram.st", "--table", "constantprogram.gtt")
            .directory("../geteta/examples/constantprogram")
            .check()
    }

    @Test
    fun minmax_minimal() {
        getetaTester("-c", "MinMax.st", "--table", "MinMax_Minimal.gtt")
            .directory("../geteta/examples/MinMax")
            .check()
    }

    @Test
    fun minmax() {
        getetaTester("-c", "MinMax.st", "--table", "MinMax.gtt")
            .directory("../geteta/examples/MinMax")
            .check()
    }

    @Test
    fun minmax_broken() {
        getetaTester("-c", "MinMax.st", "--table", "MinMax_Broken.gtt")
            .directory("../geteta/examples/MinMax")
            .check()
    }

    @Test
    fun cexPrinter() {
        getetaTester("--row-map", "--cexout", "-t", "cycles_wrong.gtt", "-c", "cycles.st")
            .directory("../geteta/examples/cycles")
            .check()
    }
}

class RetetaIntegrationTests {
    @Test
    fun help() = retetaTester("--help").check()

    @Test
    @Disabled
    fun counter() {
        retetaTester(
            "--print-augmented-programs",
            "-t",
            "table.tt.txt",
            "-P",
            "OneCnt.st",
            "-P",
            "TwoCnt.st",
        )
            .directory("../geteta/examples/RTT_counter")
            .check()
    }
}
