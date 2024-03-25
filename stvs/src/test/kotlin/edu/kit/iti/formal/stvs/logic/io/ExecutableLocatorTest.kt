package edu.kit.iti.formal.stvs.logic.io

import edu.kit.iti.formal.stvs.*
import edu.kit.iti.formal.stvs.logic.io.ExecutableLocator.findExecutableFile
import org.junit.Assert
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.io.File
import java.util.*

/**
 * Created by csicar on 20.07.17.
 */
class ExecutableLocatorTest {
    @Test
    @Throws(Exception::class)
    fun testPathWithZ3Linux() {
        TestUtils.assumeZ3Exists()

        val z3 = findExecutableFile("z3")
        Assertions.assertEquals(Optional.of(File("/usr/bin/z3")), z3)
        println(z3.toString())
    }

    @Test
    @Throws(Exception::class)
    fun testPathWithZ3LinuxString() {
        TestUtils.assumeNuXmvExists()

        val nuXmv = findExecutableFile("nuXmv")
        Assertions.assertEquals(Optional.of(File("/usr/local/bin/nuXmv")), nuXmv)
        println(nuXmv.toString())
    }

    @Test
    @Throws(Exception::class)
    fun name() {
        val empty = findExecutableFile("other")
        Assertions.assertEquals(Optional.empty<Any>(), empty)
    }
}