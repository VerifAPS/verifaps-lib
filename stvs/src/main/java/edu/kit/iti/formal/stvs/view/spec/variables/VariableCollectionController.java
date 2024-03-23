package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator;
import edu.kit.iti.formal.stvs.model.common.FreeVariableProblem;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.spec.variables.clipboard.Json;
import javafx.beans.Observable;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.scene.control.*;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.scene.input.*;
import javafx.util.converter.DefaultStringConverter;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * This is a controller for {@link VariableCollection}.
 *
 * @author Philipp
 */
public class VariableCollectionController implements Controller {

    private static final DataFormat JSON_MIME_TYPE = new DataFormat("application/json");
    private FreeVariableList freeVariableList;
    private FreeVariableListValidator validator;
    private VariableCollection view;
    private ContextMenu contextMenu;

    /**
     * Creates an instance with a predefined list of variables.
     * The available types in code must be known for validation purposes.
     *
     * @param codeTypes        Available code types
     * @param freeVariableList Predefined free variables
     */
    public VariableCollectionController(ObjectProperty<List<Type>> codeTypes,
                                        FreeVariableList freeVariableList) {
        this.freeVariableList = freeVariableList;
        this.validator = new FreeVariableListValidator(codeTypes, freeVariableList);

        this.contextMenu = new ContextMenu();
        this.view = new VariableCollection();

    /* Set up context menu */
        this.contextMenu = new ContextMenu();

        MenuItem menuItemAdd = new MenuItem("Add Variable");
        menuItemAdd.setOnAction(this::onAddVariableClicked);
        menuItemAdd.setAccelerator(new KeyCodeCombination(KeyCode.ADD));
        contextMenu.getItems().add(menuItemAdd);

        MenuItem menuItemDelete = new MenuItem("Delete Variable");
        menuItemDelete.setOnAction(this::onDeleteVariableClicked);
        menuItemDelete.setAccelerator(new KeyCodeCombination(KeyCode.DELETE));
        contextMenu.getItems().add(menuItemDelete);

        view.getFreeVariableTableView().setContextMenu(contextMenu);
        view.getFreeVariableTableView().setRowFactory(this::rowFactory);

        view.getNameTableColumn().setCellValueFactory(data -> data.getValue().nameProperty());
        view.getTypeTableColumn().setCellValueFactory(data -> data.getValue().typeProperty());
        view.getConstraintTableColumn()
                .setCellValueFactory(data -> data.getValue().constraintProperty());

        view.getNameTableColumn().setCellFactory(this::cellFactory);
        view.getTypeTableColumn().setCellFactory(this::cellFactory);
        view.getConstraintTableColumn().setCellFactory(this::cellFactory);

        view.getFreeVariableTableView().setItems(freeVariableList.getVariables());


        view.getBtnAddRow().setOnAction(this::onAddVariableClicked);
        view.getBtnRemoveRow().setOnAction(this::onDeleteVariableClicked);

    }

    private void onDeleteVariableClicked(ActionEvent actionEvent) {
        TableView<FreeVariable> tableView = view.getFreeVariableTableView();
        List<FreeVariable> newList = new LinkedList<>();
        ObservableList<Integer> sm = tableView.getSelectionModel().getSelectedIndices();
        for (int i = 0; i < tableView.getItems().size(); i++) {
            if (!sm.contains(i)) {
                newList.add(tableView.getItems().get(i));
            }
        }
        tableView.getItems().setAll(newList);

        // naive implementation does not work, if two rows are equals (in name, type and constraint)
        //tableView.getItems().removeAll(tableView.getSelectionModel().getSelectedItems());
        tableView.getSelectionModel().clearSelection();
    }

    private void onAddVariableClicked(ActionEvent actionEvent) {
        freeVariableList.getVariables().add(new FreeVariable("variable", "BOOL"));
    }

    @Override
    public VariableCollection getView() {
        return view;
    }

    public FreeVariableList getFreeVariableList() {
        return freeVariableList;
    }

    public FreeVariableListValidator getValidator() {
        return validator;
    }

    private TableCell<FreeVariable, String> cellFactory(
            TableColumn<FreeVariable, String> tableColumn) {
        return new TextFieldTableCell<FreeVariable, String>(new DefaultStringConverter()) {
            {
                validator.problemsProperty().addListener((Observable o) -> onProblemsChanged());
                getStyleClass().add("freevar");
                onProblemsChanged();
            }

            private void configureProblematic(String tooltip) {
                getStyleClass().remove("freevar-problem");
                getStyleClass().add("freevar-problem");
                setTooltip(new Tooltip(tooltip));
            }

            private void configureUnproblematic() {
                getStyleClass().remove("freevar-problem");
                setTooltip(null);
            }

            @Override
            public void updateItem(String item, boolean empty) {
                super.updateItem(item, empty);
                onProblemsChanged();
            }

            private void onProblemsChanged() {
                if (!isEmpty()) {
                    List<FreeVariableProblem> problems = validator.problemsProperty().get()
                            .getOrDefault(getTableRow().getItem(), Collections.emptyList());
                    if (problems.isEmpty()) {
                        configureUnproblematic();
                    } else {
                        configureProblematic(String.join("\n\n", problems.stream()
                                .map(FreeVariableProblem::getGuiMessage).collect(Collectors.toList())));
                    }
                }
            }
        };
    }

    private TableRow<FreeVariable> rowFactory(TableView<FreeVariable> tableView) {
        TableRow<FreeVariable> row = new TableRow<>();

        row.setOnDragDetected(event -> {
            ObservableList<FreeVariable> selected = tableView.getSelectionModel().getSelectedItems();
            if (!selected.isEmpty()) {
                String serializedSelection = Json.stringFromRealFreeVariables(selected);
                Dragboard db = tableView.startDragAndDrop(TransferMode.MOVE);
                ClipboardContent cc = new ClipboardContent();
                cc.putString(serializedSelection);
                cc.put(JSON_MIME_TYPE, serializedSelection);
                db.setContent(cc);

                event.consume();
            }
        });

        row.setOnDragOver(event -> {
            Dragboard db = event.getDragboard();
            if (db.hasContent(JSON_MIME_TYPE)) {
                event.acceptTransferModes(TransferMode.COPY_OR_MOVE);
                event.consume();
            }
        });

        row.setOnDragDropped(event -> {
            Dragboard db = event.getDragboard();
            if (db.hasContent(JSON_MIME_TYPE)) {
                String dragboardContent = db.getContent(JSON_MIME_TYPE).toString();
                List<FreeVariable> droppedVariables = Json.stringToRealFreeVariables(dragboardContent);

                tableView.getItems().removeIf(freeVariable -> droppedVariables.stream()
                        .anyMatch(var -> var.getName().equals(freeVariable.getName())));

                int dropIndex = row.getIndex();
                tableView.getItems().addAll(Math.min(dropIndex, tableView.getItems().size()),
                        droppedVariables);

                tableView.getSelectionModel().clearSelection();
                tableView.getSelectionModel().selectRange(dropIndex, dropIndex + droppedVariables.size());

                event.setDropCompleted(true);
                event.consume();
            }
        });
        return row;
    }

}
