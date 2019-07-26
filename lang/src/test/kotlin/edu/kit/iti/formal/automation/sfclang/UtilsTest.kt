package edu.kit.iti.formal.automation.sfclang

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
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
 * #L%
 */

import org.junit.jupiter.api.Assertions
 import org.junit.jupiter.api.Test

/**
 * @author Alexander Weigl
 * @version 1 (25.06.17)
 */
class UtilsTest {
    @Test
    @Throws(Exception::class)
    fun split1() {
        val (dt, radix, value) = split("abc#12#111")
        Assertions.assertEquals("abc", dt)
        Assertions.assertEquals(12, radix)
        Assertions.assertEquals("111", value)
    }

    @Test
    @Throws(Exception::class)
    fun split2() {
        val (dt, r, v) = split("12#111")
        Assertions.assertFalse(dt != null)
        Assertions.assertEquals(12, r)
        Assertions.assertEquals("111", v)
    }


    @Test
    @Throws(Exception::class)
    fun split3() {
        val a = split("abc#def")
        System.out.println(a)
        Assertions.assertTrue(a.prefix != null)
        Assertions.assertFalse(a.ordinal != null)
        Assertions.assertEquals("abc", a.prefix)
        Assertions.assertEquals("def", a.value)
    }

}
