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
package edu.kit.iti.formal.stvs.model.config

import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConfigImporter
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * Created by bal on 26.02.17.
 */
class GlobalConfigTest {
    private var config: GlobalConfig =
        ImporterFacade.importConfig(XmlConfigImporter::class.java.getResourceAsStream("config_valid_complete.xml")!!)

    @Test
    @Throws(Exception::class)
    fun setAll() {
        val clone = GlobalConfig()
        clone.setAll(config)
        Assertions.assertEquals(clone, config)
    }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        val identical: GlobalConfig =
            ImporterFacade.importConfig(
                XmlConfigImporter::class.java.getResourceAsStream("config_valid_complete.xml")!!,
            )
        Assertions.assertEquals(identical, config)
        Assertions.assertNotEquals(null, config)
        Assertions.assertEquals(config, config)
        identical.windowHeight = 1000
        Assertions.assertNotEquals(config, identical)
    }

    @Test
    fun testHashCode() {
        val identical: GlobalConfig = ImporterFacade.importConfig(
            XmlConfigImporter::class.java.getResourceAsStream("config_valid_complete.xml")!!,
        )
        Assertions.assertEquals(identical.hashCode().toLong(), config.hashCode().toLong())
        Assertions.assertEquals(config.hashCode().toLong(), config.hashCode().toLong())
        identical.windowHeight = 1000
        Assertions.assertNotEquals(config.hashCode().toLong(), identical.hashCode().toLong())
    }
}