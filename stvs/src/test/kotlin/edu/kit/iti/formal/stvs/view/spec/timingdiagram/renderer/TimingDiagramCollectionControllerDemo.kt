package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer

import org.junit.jupiter.api.Tag
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConcreteSpecImporter
import edu.kit.iti.formal.stvs.model.common.Selection
import edu.kit.iti.formal.stvs.model.common.SelectionClickListener
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.view.JavaFxTest
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController
import javafx.application.Application
import javafx.beans.InvalidationListener
import javafx.beans.Observable
import javafx.scene.Scene
import javafx.scene.control.TextArea
import javafx.scene.layout.VBox
import org.junit.Test
import java.io.File
import java.io.FileInputStream
import java.util.function.Supplier

/**
 * Created by leonk on 02.02.2017.
 */
@Tag("demo")
class TimingDiagramCollectionControllerDemo {
    @Test
    fun javaFxTest() {
        JavaFxTest.setToBeViewed(Supplier<Scene?> { this.simpleScene() })
        Application.launch(JavaFxTest::class.java)
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

            val selection = Selection()
            val controller = TimingDiagramCollectionController(importedSpec, selection)

            val console = TextArea()

            selection.columnProperty.addListener(InvalidationListener { change: Observable? ->
                console.appendText("Selection column set to: " + selection.column + "\n")
            })
            selection.rowProperty.addListener(InvalidationListener { change: Observable? ->
                console.appendText("Selection row set to: " + selection.row + "\n")
            })
            selection.setOnTimingDiagramSelectionClickListener(SelectionClickListener { col: String?, cycle: Int? ->
                console.appendText(
                    "Clicked on $col $cycle"
                )
            })

            val root: VBox = VBox()
            root.getChildren().addAll(controller.view, console)
            val scene: Scene = Scene(root, 800.0, 600.0)
            //scene.getStylesheets().add(this.getClass().getResource("style.css").toExternalForm());
            return scene
        } catch (e: Exception) {
            e.printStackTrace()
            return null
        }
    }
}