package edu.kit.iti.formal.stvs.view.spec

import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.table.HybridRow
import edu.kit.iti.formal.stvs.view.ViewUtils
import edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableView
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionView
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollection
import javafx.beans.property.SimpleBooleanProperty
import javafx.event.EventHandler
import javafx.geometry.Pos
import javafx.scene.Cursor
import javafx.scene.Node
import javafx.scene.control.*
import javafx.scene.input.MouseEvent
import javafx.scene.layout.*
import javafx.scene.paint.Color
import org.kordamp.ikonli.fontawesome5.FontAwesomeRegular
import org.kordamp.ikonli.fontawesome5.FontAwesomeSolid
import org.kordamp.ikonli.javafx.FontIcon
import java.util.function.Supplier

/**
 * This is the view that displays a specification.
 *
 * @author Carsten Csiky
 */
class SpecificationView : VBox(), Lockable {
    private val variablesPane = StackPane()
    private val tablePane = StackPane()
    private val timingDiagramPane = StackPane()


    //private final SplitPane splitPane = new SplitPane();
    private val buttonBox = HBox(5.0)

    val startButton: Button

    val startConcretizerButton: Button
    var variableCollection: VariableCollection? = null
        set(value) {
            field = value
            variablesPane.children.setAll(this.variableCollection)
        }

    private var tableView: SpecificationTableView? = null
    var diagram: TimingDiagramCollectionView? = null
        set(value) {
            field = value
            if (value == null) {
                timingDiagramPane.children.setAll()
            } else {
                timingDiagramPane.children.setAll(diagram)
                AnchorPane.setLeftAnchor(diagram, 0.0)
                AnchorPane.setRightAnchor(diagram, 0.0)
                AnchorPane.setTopAnchor(diagram, 0.0)
                AnchorPane.setBottomAnchor(diagram, 0.0)
            }
        }

    /**
     * Creates an instance.
     */
    init {
        //splitPane = new SplitPane();
        //SplitPane.setResizableWithParent(variablesPane,true);

        buttonBox.styleClass.addAll("button-box", "verification-action-buttons", "action-buttons")
        startButton = Button()
        startConcretizerButton = Button()
        setVerificationButtonPlay()
        setConcretizerButtonStart()
        children.add(buttonBox)
        buttonBox.children.addAll(startButton, startConcretizerButton)
        buttonBox.alignment = Pos.TOP_RIGHT

        //splitPane.setOrientation(Orientation.VERTICAL);
        //splitPane.getItems().addAll(variablesPane, tablePane, timingDiagramPane);
        //splitPane.setDividerPosition(0, 0.25);
        //splitPane.setDividerPosition(1, 0.5);
        //getChildren().addAll(splitPane);
        val scrollPane = ScrollPane(
            VBox(
                variablesPane,
                ResizerPane { variableCollection!!.content }, tablePane,
                ResizerPane { tableView!!.content }, timingDiagramPane
            )
        )
        children.addAll(scrollPane)
        scrollPane.hbarPolicy = ScrollPane.ScrollBarPolicy.NEVER
        scrollPane.isFitToWidth = true
        setVgrow(scrollPane, Priority.ALWAYS)
        ViewUtils.setupClass(this)
    }

    /**
     * Set verification button to a state that signals that the verification can be started.
     */
    fun setVerificationButtonPlay() {
        val icon = FontIcon(FontAwesomeSolid.PLAY)
        icon.fill = Color.MEDIUMSEAGREEN
        startButton.text = "Verify"
        startButton.graphic = icon
        startButton.styleClass.addAll("action", "action-verification")
    }

    /**
     * Set verification button to a state that signals that the verification can be stopped.
     */
    fun setVerificationButtonStop() {
        val icon = FontIcon(FontAwesomeSolid.STOP)
        icon.fill = Color.INDIANRED
        startButton.text = "Stop Verification"
        startButton.graphic = icon
    }

    /**
     * Set concretizer button to a state that signals that the concretizer can be started.
     */
    fun setConcretizerButtonStart() {
        val icon = FontIcon(FontAwesomeRegular.CHART_BAR)
        icon.fill = Color.MEDIUMSEAGREEN
        startConcretizerButton.text = "Concretize"
        startConcretizerButton.styleClass.addAll("action", "action-concretize")
        startConcretizerButton.graphic = icon
    }

    /**
     * Set concretizer button to a state that signals that the concretizer can be stopped.
     */
    fun setConcretizerButtonStop() {
        val icon = FontIcon(FontAwesomeSolid.STOP)
        icon.fill = Color.INDIANRED
        startConcretizerButton.text = "Stop Concretization"
        startConcretizerButton.graphic = icon
    }

    val table: TableView<HybridRow>?
        get() = tableView?.tableView

    /**
     * Sets the child view that displays the table to display the given table.
     *
     * @param tableView table to show
     */
    fun setTable(tableView: SpecificationTableView?) {
        this.tableView = tableView
        tablePane.children.setAll(tableView)
    }


    /**
     * Displays a placeholder in the timing diagram area.
     */
    fun setEmptyDiagram() {
        val pane = GridPane()
        pane.alignment = Pos.CENTER
        pane.hgap = 10.0
        pane.vgap = 10.0
        pane.add(Label("No timing diagram available."), 0, 0)
        setEmptyDiagram(TitledPane("Timing Diagram", pane))
    }

    /**
     * Displays an arbitrary placeholder node in the timing diagram area.
     *
     * @param emptyDiagram Node that should be displayed
     */
    fun setEmptyDiagram(emptyDiagram: Node?) {
        this.diagram = null
        timingDiagramPane.children.setAll(emptyDiagram)

        //timingDiagramPane.getChildren().add(emptyDiagram);
        AnchorPane.setLeftAnchor(emptyDiagram, 0.0)
        AnchorPane.setRightAnchor(emptyDiagram, 0.0)
        AnchorPane.setTopAnchor(emptyDiagram, 0.0)
        AnchorPane.setBottomAnchor(emptyDiagram, 0.0)
    }


    override var editable: Boolean
        get() = false
        set(b) {}

    override val editableProperty = SimpleBooleanProperty(false)

    fun onVerificationButtonClicked(constraintSpec: ConstraintSpecification, type: VerificationEvent.Type) {
        startButton.fireEvent(VerificationEvent(constraintSpec, type))
    }

    private inner class ResizerPane(nodeSupplier: Supplier<Node>) : Separator() {
        private var startY = 0.0
        private var startHeight = 0.0

        init {
            cursor = Cursor.N_RESIZE
            height = 5.0

            onMousePressed = EventHandler { event: MouseEvent ->
                startY = event.screenY
                startHeight = (nodeSupplier.get() as Region).height
            }

            onMouseDragged = EventHandler { event: MouseEvent ->
                event.consume()
                val diff = event.screenY - startY
                //System.out.println("DIFF" + diff + "  " + startHeight + diff);
                (nodeSupplier.get() as Region).prefHeight = startHeight + diff
            }
        }
    }
}
