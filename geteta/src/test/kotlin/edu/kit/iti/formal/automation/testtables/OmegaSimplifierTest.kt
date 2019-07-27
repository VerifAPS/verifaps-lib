/**
 * geteta
 *
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl></weigl>@kit.edu>
 *
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http:></http:>//www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables

import edu.kit.iti.formal.automation.testtables.algorithms.OmegaSimplifier
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.DisplayName
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.CsvSource

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
class OmegaSimplifierTest : TableTester() {
    @ParameterizedTest(name = "{index} {0}")
    @CsvSource("simplify1| e, f, g, h",
            "simplify2 | f, g, h, i",
            "simplify3 | r, s, t",
            delimiter = '|')
    fun run(tableName: String, exp: String) {
        val ignored = test(tableName)
        Assertions.assertEquals(exp, ignored)
    }

    private fun test(tableName: String): String {
        val gtt = getTable(tableName)
        val os = OmegaSimplifier(gtt)
        os.run()
        return os.ignored.joinToString { it.id }
    }
}