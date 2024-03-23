package edu.kit.iti.formal.stvs.view.spec.variables;

import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIconView;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.view.ViewUtils;
import javafx.scene.Node;
import javafx.scene.control.*;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;

/**
 * This is the view that displays free variables and offers editing them.
 *
 * @author Philipp
 * @author Alexander Weigl
 */
public class VariableCollection extends TitledPane {
    private final TableView<FreeVariable> freeVariableTableView = new TableView<>();
    private final TableColumn<FreeVariable, String> nameTableColumn = new TableColumn<>("Name");
    private final TableColumn<FreeVariable, String> typeTableColumn = new TableColumn<>("Type");
    private final TableColumn<FreeVariable, String> constraintTableColumn = new TableColumn<>("Constraint");

    private final BorderPane content = new BorderPane();
    private final ToolBar toolBar = new ToolBar();
    private final Button btnRemoveRow = new Button("Remove Rows",
            new FontAwesomeIconView(FontAwesomeIcon.MINUS_SQUARE));
    private final Button btnAddRow = new Button("Add Rows",
            new FontAwesomeIconView(FontAwesomeIcon.PLUS_SQUARE));
    //private final Button btnRemoveRow = new Button();


    /**
     * Creates an instance of this view.
     */
    public VariableCollection() {
        setText("Global Variables");
        this.freeVariableTableView.setId("VariableCollectionTableView");
        ViewUtils.setupView(this);
        setExpanded(false);

        nameTableColumn.prefWidthProperty().bind(freeVariableTableView.widthProperty().multiply(0.4));
        typeTableColumn.prefWidthProperty().bind(freeVariableTableView.widthProperty().multiply(0.4));
        constraintTableColumn.prefWidthProperty()
                .bind(freeVariableTableView.widthProperty().multiply(0.2));

        nameTableColumn.setUserData(Column.NAME);
        typeTableColumn.setUserData(Column.TYPE);
        constraintTableColumn.setUserData(Column.CONSTRAINT);

        freeVariableTableView.setEditable(true);
        freeVariableTableView.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);
        freeVariableTableView.getColumns().setAll(nameTableColumn, typeTableColumn, constraintTableColumn);

        Region stretch = new Region();
        HBox.setHgrow(stretch, Priority.ALWAYS);

        //this.overviewLabel.getStyleClass().addAll("freevar", "overview-label");
        this.freeVariableTableView.getStyleClass().addAll("freevar", "variable-table-view");
        freeVariableTableView.setPrefHeight(100.0);
        setContent(content);
        content.setCenter(freeVariableTableView);
        content.setTop(toolBar);

        btnAddRow.setContentDisplay(ContentDisplay.GRAPHIC_ONLY);
        btnRemoveRow.setContentDisplay(ContentDisplay.GRAPHIC_ONLY);
        toolBar.getItems().setAll(stretch,btnAddRow, btnRemoveRow);
        setMinHeight(0);
        setMaxHeight(1000);
    }

    public TableView<FreeVariable> getFreeVariableTableView() {
        return freeVariableTableView;
    }

    public void removeVariableView(Node view) {
        this.getChildren().removeAll(view);
    }

    public TableColumn<FreeVariable, String> getNameTableColumn() {
        return nameTableColumn;
    }

    public TableColumn<FreeVariable, String> getTypeTableColumn() {
        return typeTableColumn;
    }

    public TableColumn<FreeVariable, String> getConstraintTableColumn() {
        return constraintTableColumn;
    }


    public Button getBtnAddRow() {
        return btnAddRow;
    }

    public Button getBtnRemoveRow() {
        return btnRemoveRow;
    }

    public enum Column {
        NAME, TYPE, CONSTRAINT
    }
}
