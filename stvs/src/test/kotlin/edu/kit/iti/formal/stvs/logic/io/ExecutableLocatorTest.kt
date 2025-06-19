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
package edu.kit.iti.formal.stvs.logic.io

import edu.kit.iti.formal.stvs.TestUtils
import edu.kit.iti.formal.stvs.logic.io.ExecutableLocator.findExecutableFile
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test
import java.io.File

/**
 * Created by csicar on 20.07.17.
 */
@Disabled
class ExecutableLocatorTest {
    @Test
    @Throws(Exception::class)
    fun testPathWithZ3Linux() {
        TestUtils.assumeZ3Exists()

        val z3 = findExecutableFile("z3")
        Assertions.assertEquals(File("/usr/bin/z3"), z3)
        println(z3.toString())
    }

    @Test
    @Throws(Exception::class)
    fun testPathWithZ3LinuxString() {
        TestUtils.assumeNuXmvExists()

        val nuXmv = findExecutableFile("nuXmv")
        Assertions.assertEquals(File("/usr/local/bin/nuXmv"), nuXmv)
        println(nuXmv.toString())
    }

    @Test
    @Throws(Exception::class)
    fun name() {
        val empty = findExecutableFile("other")
        Assertions.assertEquals(null, empty)
    }
}