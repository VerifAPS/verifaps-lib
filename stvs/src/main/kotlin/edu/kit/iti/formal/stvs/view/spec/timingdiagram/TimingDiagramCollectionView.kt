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
package edu.kit.iti.formal.stvs.view.spec.timingdiagram

import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.beans.Observable
import javafx.beans.value.ObservableValue
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.Node
import javafx.scene.Scene
import javafx.scene.chart.NumberAxis
import javafx.scene.control.*
import javafx.scene.layout.*
import javafx.scene.text.TextAlignment
import javafx.stage.Modality
import javafx.stage.Stage
import javafx.stage.StageStyle
import javafx.stage.WindowEvent
import org.kordamp.ikonli.fontawesome5.FontAwesomeSolid
import org.kordamp.ikonli.javafx.FontIcon

/**
 * Represents the view for the collection of multiple timing diagrams.
 *
 * @author Leon Kaucher
 * @author Carsten Csiky
 * @author Alexander Weigl
 */
class TimingDiagramCollectionView : VBox() {
    private val content = VBox()
    val outdatedMessage: HBox
    val diagramContainer: VBox = VBox() // Container that holds the diagrams
    private val yaxisContainer = Pane() // Container that holds yAxis for each diagram
    val labelContainer: Pane = Pane() // Container that holds titles for each diagram

    // Container that holds yaxisStickRightContainer and diagramContainer
    private val axisDiagramContainer = SplitPane()
    private val globalAxisContainer = Pane() // Container that holds the global xaxis
    val xaxis: NumberAxis = NumberAxis(0.0, 10.0, 1.0)
    val xscrollBar: ScrollBar = ScrollBar()
    private val tp = TitledPane()

    /**
     * Creates a View that holds all containers for multiple [ TimingDiagrams][TimingDiagramCollectionView]. It holds a container for variable titles and y Axis which can be pulled out on
     * the left.
     */
    init {
        tp.text = "Timing Diagram"
        children.addAll(tp)

        styleClass.add("collectionView")
        // Create the message at the top of all diagrams, that is visible when the diagram is outdated
        val outdatedLabel = Label("This Timing-Diagram is outdated.")
        outdatedLabel.styleClass.add("outdatedLabel")
        val outdatedIcon: Node = FontIcon(FontAwesomeSolid.EXCLAMATION_TRIANGLE)
        outdatedIcon.styleClass.add("outdatedIcon")
        outdatedMessage = HBox(outdatedIcon, outdatedLabel)
        outdatedMessage.styleClass.add("outdatedMessage")

        val scrollPane = ScrollPane()
        content.children.addAll(outdatedMessage, scrollPane, globalAxisContainer, xscrollBar)
        tp.content = content

        globalAxisContainer.children.add(xaxis)

        // setPadding(new Insets(0, 0, 0, 0));
        val yaxisStickRightContainer = AnchorPane()
        yaxisStickRightContainer.children.addAll(labelContainer, yaxisContainer)
        yaxisStickRightContainer.minWidth = 0.0

        AnchorPane.setRightAnchor(yaxisContainer, 0.0)
        AnchorPane.setLeftAnchor(labelContainer, 0.0)
        AnchorPane.setBottomAnchor(labelContainer, 0.0)
        AnchorPane.setTopAnchor(labelContainer, 0.0)
        axisDiagramContainer.items.addAll(yaxisStickRightContainer, diagramContainer)
        scrollPane.content = axisDiagramContainer
        scrollPane.isFitToWidth = true
        // Positions the xaxis so it always aligns with the diagrams
        diagramContainer.layoutBoundsProperty().addListener { change: Observable? ->
            val diagram = diagramContainer.localToScene(diagramContainer.layoutBounds)
            val axisContainer =
                globalAxisContainer.localToScene(globalAxisContainer.layoutBounds)
            xaxis.layoutXProperty().setValue(diagram.minX - axisContainer.minX)
        }
        xaxis.styleClass.add("globalXAxis")
        globalAxisContainer.styleClass.add("globalXAxisContainer")
        xaxis.prefWidthProperty().bind(diagramContainer.widthProperty())
        axisDiagramContainer.setDividerPosition(0, 0.1)

        /*needed as a workaround for a bug in JavaFx on Linux, where a LineChart Axis only
    updates, once it has been moved. The moving only "counts" if the Window is shown
    see issue #28*/
        axisDiagramContainer.sceneProperty()
            .addListener { observableValue: ObservableValue<out Scene?>?, old: Scene?, scene: Scene? ->
                if (scene != null) {
                    scene.window.onShown = EventHandler { windowEvent: WindowEvent? ->
                        axisDiagramContainer.setDividerPosition(0, 0.1)
                    }
                }
            }

        scrollPane.styleClass.add("noborder-scroll-pane")
        labelContainer.styleClass.add("labelContainer")

        tp.textAlignment = TextAlignment.LEFT
        tp.isWrapText = false
        val btnOpenExternal = Button()
        btnOpenExternal.graphic = FontIcon(FontAwesomeSolid.EXTERNAL_LINK_ALT)
        btnOpenExternal.onAction = EventHandler { event: ActionEvent -> this.showInDialog(event) }
        tp.graphic = btnOpenExternal
        tp.contentDisplay = ContentDisplay.RIGHT

        ViewUtils.setupView(this)
    }

    fun getyAxisContainer(): Pane = yaxisContainer

    private fun showInDialog(event: ActionEvent) {
        val s = Stage(StageStyle.DECORATED)
        s.title = tp.text
        s.initModality(Modality.APPLICATION_MODAL)
        s.minHeight = 640.0
        s.minHeight = 480.0
        // s.setFullScreen(true);
        s.isMaximized = true
        // TableView<HybridRow> newView = new TableView<>(tableView.getItems());
        val root = BorderPane(content)
        tp.content = Label("opened externally")
        val bb = ButtonBar()
        root.top = bb
        s.scene = Scene(root)
        val yesButton = Button("Close")
        ButtonBar.setButtonData(yesButton, ButtonBar.ButtonData.CANCEL_CLOSE)
        bb.buttons.addAll(yesButton)
        yesButton.onAction = EventHandler { e: ActionEvent? -> s.hide() }
        s.showAndWait()
        tp.content = content
    }
}