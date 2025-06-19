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
package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer

import edu.kit.iti.formal.stvs.logic.io.xml.XmlConcreteSpecImporter
import edu.kit.iti.formal.stvs.model.common.Selection
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.view.JavaFxTest
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController
import javafx.application.Application
import javafx.beans.Observable
import javafx.scene.Scene
import javafx.scene.control.TextArea
import javafx.scene.layout.VBox
import org.junit.Test
import org.junit.jupiter.api.Tag
import java.io.File
import java.io.FileInputStream

/**
 * Created by leonk on 02.02.2017.
 */
@Tag("demo")
class TimingDiagramCollectionControllerDemo {
    @Test
    fun javaFxTest() {
        JavaFxTest.setToBeViewed { this.simpleScene() }
        Application.launch(JavaFxTest::class.java)
    }

    private fun simpleScene(): Scene? {
        try {
            val importer = XmlConcreteSpecImporter(listOf(TypeInt, TypeBool))
            val inputStream = FileInputStream(
                File(
                    TimingDiagramCollectionControllerDemo::class.java.getResource("spec_concrete_valid_1.xml")!!.toURI()
                )
            )
            val importedSpec: ConcreteSpecification = importer.doImport(inputStream)

            val selection = Selection()
            val controller = TimingDiagramCollectionController(importedSpec, selection)

            val console = TextArea()

            selection.columnProperty.addListener { change: Observable? ->
                console.appendText("Selection column set to: " + selection.column + "\n")
            }
            selection.rowProperty.addListener { change: Observable? ->
                console.appendText("Selection row set to: " + selection.row + "\n")
            }
            selection.setOnTimingDiagramSelectionClickListener { col: String?, cycle: Int? ->
                console.appendText(
                    "Clicked on $col $cycle"
                )
            }

            val root = VBox()
            root.getChildren().addAll(controller.view, console)
            val scene = Scene(root, 800.0, 600.0)
            // scene.getStylesheets().add(this.getClass().getResource("style.css").toExternalForm());
            return scene
        } catch (e: Exception) {
            e.printStackTrace()
            return null
        }
    }
}