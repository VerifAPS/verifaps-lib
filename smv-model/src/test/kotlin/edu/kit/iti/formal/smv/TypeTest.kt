package edu.kit.iti.formal.smv

/*-
 * #%L
 * smv-model
 * %%
 * Copyright (C) 2016 Alexander Weigl
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

import junit.framework.Assert
import org.junit.Test

import java.util.Arrays

/**
 * @author Alexander Weigl
 * @version 1 (15.12.16)
 */
class TypeTest {
    @Test
    fun testOutput() {
        val u10 = SMVWordType(false, 10)
        val s0 = SMVWordType(true, 0)
        val b = SMVTypes.BOOLEAN
        val e = EnumType(Arrays.asList("a", "b", "c"))

        Assert.assertEquals("unsigned word[10]", u10.repr())
        Assert.assertEquals("boolean", b.repr())
        Assert.assertEquals("signed word[0]", s0.repr())
        Assert.assertEquals("{a, b, c}", e.repr())


    }

}
