/**
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl></weigl>@kit.edu>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http:></http:>//www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.io.xmv

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import org.junit.Assert.assertEquals
import org.junit.Assume
import org.junit.Before
import org.junit.Test
import java.io.IOException
import java.io.InputStreamReader

/**
 * @author Alexander Weigl
 * @version 1 (03.01.17)
 */
class NuXMVOutputParserTest {
    private var op: NuXMVOutputParser? = null

    @Before
    @Throws(IOException::class)
    fun setup() {
        val resourceAsStream = javaClass.getResourceAsStream("/log_50.txt")
        Assume.assumeNotNull(resourceAsStream)
        val res = InputStreamReader(resourceAsStream)
        val content = res.readText()
        op = NuXMVOutputParser(content)
    }


    @Test
    @Throws(Exception::class)
    fun run() {
        Assume.assumeTrue(op != null)
        val ce = op!!.run()
        assertEquals(57, ce.step.size.toLong())
    }

}
