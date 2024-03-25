package edu.kit.iti.formal.stvs.view.spec.timingdiagram

import edu.kit.iti.formal.stvs.Demo
import edu.kit.iti.formal.stvs.model.common.SelectionClickListener
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.view.JavaFxTest
import javafx.beans.InvalidationListener
import javafx.beans.Observable
import javafx.scene.Scene
import javafx.scene.layout.VBox
import java.io.File
import java.io.FileInputStream

/**
 * Created by leonk on 02.02.2017.
 */
@org.junit.experimental.categories.Category(Demo::class)
class TimingDiagramCollectionControllerDemo {
    @org.junit.Test
    fun javaFxTest() {
        JavaFxTest.Companion.setToBeViewed(java.util.function.Supplier<Scene?> { this.simpleScene() })
        javafx.application.Application.launch(JavaFxTest::class.java)
    }

    private fun simpleScene(): Scene? {
        try {
            val importer = XmlConcreteSpecImporter(listOf(TypeInt.INT, TypeBool.BOOL))
            val inputStream = FileInputStream(
                File(
                    TimingDiagramCollectionControllerDemo::class.java.getResource("spec_concrete_valid_1.xml")!!.toURI()
                )
            )
            val importedSpec: ConcreteSpecification = importer.doImport(inputStream)

            val selection = edu.kit.iti.formal.stvs.model.common.Selection()
            val controller = TimingDiagramCollectionController(importedSpec, selection)

            val console = javafx.scene.control.TextArea()

            selection.columnProperty().addListener(InvalidationListener { change: Observable? ->
                console.appendText("Selection column set to: " + selection.getColumn() + "\n")
            })
            selection.rowProperty().addListener(InvalidationListener { change: javafx.beans.Observable? ->
                console.appendText("Selection row set to: " + selection.getRow() + "\n")
            })
            selection.setOnTimingDiagramSelectionClickListener(SelectionClickListener { col: String, cycle: Int ->
                console.appendText(
                    "Clicked on $col $cycle"
                )
            })

            val root: VBox = VBox()
            root.getChildren().addAll(controller.view, console)
            val scene: Scene = Scene(root, 800.0, 600.0)
            //scene.getStylesheets().add(this.getClass().getResource("style.css").toExternalForm());
            return scene
        } catch (e: java.lang.Exception) {
            e.printStackTrace()
            return null
        }
    }
}