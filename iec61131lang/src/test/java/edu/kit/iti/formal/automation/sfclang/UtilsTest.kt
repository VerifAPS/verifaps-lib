package edu.kit.iti.formal.automation.sfclang

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import org.junit.Assert
import org.junit.Test

/**
 * @author Alexander Weigl
 * @version 1 (25.06.17)
 */
class UtilsTest {
    @Test
    @Throws(Exception::class)
    fun split1() {
        val a = split("abc#12#111")
        Assert.assertEquals("abc", a.prefix)
        Assert.assertEquals("12", a.ordinal)
        Assert.assertEquals("111", a.value)
    }

    @Test
    @Throws(Exception::class)
    fun split2() {
        val a = split("12#111")
        System.out.println(a)
        Assert.assertFalse(a.prefix != null)
        Assert.assertEquals("12", a.ordinal)
        Assert.assertEquals("111", a.value)
    }


    @Test
    @Throws(Exception::class)
    fun split3() {
        val a = split("abc#def")
        System.out.println(a)
        Assert.assertTrue(a.prefix != null)
        Assert.assertFalse(a.ordinal != null)
        Assert.assertEquals("abc", a.prefix)
        Assert.assertEquals("def", a.value)
    }

}
