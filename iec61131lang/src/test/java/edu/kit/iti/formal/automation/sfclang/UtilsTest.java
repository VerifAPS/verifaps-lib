package edu.kit.iti.formal.automation.sfclang;

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

import org.junit.Assert;
import org.junit.Test;

import static org.junit.Assert.*;

/**
 * @author Alexander Weigl
 * @version 1 (25.06.17)
 */
public class UtilsTest {
    @Test
    public void split1() throws Exception {
        Utils.Splitted a = Utils.INSTANCE.split("abc#12#111");
        Assert.assertEquals("abc", a.prefix().get());
        Assert.assertEquals("12", a.radix().get());
        Assert.assertEquals("111", a.value().get());
    }

    @Test
    public void split2() throws Exception {
        Utils.Splitted a = Utils.INSTANCE.split("12#111");
        System.out.println(a);
        Assert.assertFalse(a.prefix().isPresent());
        Assert.assertEquals("12", a.radix().get());
        Assert.assertEquals("111", a.value().get());
    }


    @Test
    public void split3() throws Exception {
        Utils.Splitted a = Utils.INSTANCE.split("abc#def");
        System.out.println(a);
        Assert.assertTrue(a.prefix().isPresent());
        Assert.assertFalse(a.radix().isPresent());
        Assert.assertEquals("abc",a.prefix().get());
        Assert.assertEquals("def", a.value().get());
    }

}
