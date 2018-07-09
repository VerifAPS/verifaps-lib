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
package edu.kit.iti.formal.automation.testtables.io

import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.algorithms.OmegaSimplifier
import org.junit.Assert
import org.junit.Test
import javax.xml.bind.JAXBException

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
class OmegaSimplifierTest {
    @Test
    @Throws(Exception::class)
    fun run_omga_simplify1() {
        val ignored = test("simplify1.xml")
        Assert.assertEquals("5,6,7,8", ignored)
    }


    @Throws(JAXBException::class)
    private fun test(filename: String): String {
        val gtt = GetetaFacade.readTable("src/test/resources/omega/$filename")
        val os = OmegaSimplifier(gtt)
        os.run()
        return os.ignored.joinToString { it.id }
    }

    @Test
    @Throws(Exception::class)
    fun run_omga_simplify2() {
        val ignored = test("simplify2.xml")
        Assert.assertEquals("6,7,8,9", ignored)
    }

    @Test
    @Throws(Exception::class)
    fun run_omga_simplify3() {
        val ignored = test("simplify3.xml")
        Assert.assertEquals("22,23,24", ignored)
    }

}