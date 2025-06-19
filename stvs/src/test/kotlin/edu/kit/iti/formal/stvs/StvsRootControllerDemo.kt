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
package edu.kit.iti.formal.stvs.view

import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSessionImporterTest
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import javafx.application.Application
import javafx.scene.Scene
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test

/**
 * Created by csicar on 08.02.17.
 */
@Tag("demo")
class StvsRootControllerDemo {
    private fun simpleScene(sessionFile: String): Scene {
        var rootModel: StvsRootModel? = StvsRootModel()
        try {
            rootModel = ImporterFacade.importSession(
                XmlSessionImporterTest::class.java.getResourceAsStream(sessionFile)!!,
                GlobalConfig(),
                History(),
            )
        } catch (e: Exception) {
            e.printStackTrace()
        }

        val scene = StvsMainScene(rootModel!!)

        return scene.scene
    }

    @Test
    fun superSimpleTestcase() {
        JavaFxTest.runView { simpleScene("session_super_simple_testcase.xml") }
    }

    @Test
    fun testDemo() {
        JavaFxTest.runView { simpleScene("demo_session.xml") }
    }

    @Test
    fun javaFxTest() {
        JavaFxTest.setToBeViewed { simpleScene("session_valid_2.xml") }
        Application.launch(JavaFxTest::class.java)
    }
}