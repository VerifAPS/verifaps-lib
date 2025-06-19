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
import edu.kit.iti.formal.automation.Check
import java.io.File
import kotlin.test.Test

/**
 *
 * @author Alexander Weigl
 * @version 1 (18.03.18)
 */
class FlycheckTest {
    @Test
    fun test() {
        val file = File("src/test/resources/test.st").absolutePath
        Check.main(arrayOf(file))
    }

    @Test
    fun testOO() {
        val file = File("src/test/resources/testoo.st").absolutePath
        Check.main(arrayOf(file))
    }
}
