package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.view.spec.Lockable;
import edu.kit.iti.formal.stvs.view.spec.table.rowActions.AddButtonColumn;
import edu.kit.iti.formal.stvs.view.spec.table.rowActions.CommentButtonColumn;
import edu.kit.iti.formal.stvs.view.spec.table.rowActions.RemoveButtonColumn;
import javafx.beans.property.BooleanProperty;
import javafx.scene.layout.HBox;

public class TablePane extends HBox implements Lockable {
    private TableCategory inputTable;
    private TableCategory outputTable;
    private DurationsColumn durations;
    private AddButtonColumn addButtons;
    private RemoveButtonColumn removeButtonColumn;
    private CommentButtonColumn commentButtonColumn;

    public TableCategory getInputTable() {
        return inputTable;
    }

    public void setInputTable(TableCategory inputTable) {
        this.inputTable = inputTable;
    }

    public TableCategory getOutputTable() {
        return outputTable;
    }

    public void setOutputTable(TableCategory outputTable) {
        this.outputTable = outputTable;
    }

    public DurationsColumn getDurations() {
        return durations;
    }

    public void setDurations(DurationsColumn durations) {
        this.durations = durations;
    }

    public AddButtonColumn getAddButtons() {
        return addButtons;
    }

    public void setAddButtons(AddButtonColumn addButtons) {
        this.addButtons = addButtons;
    }

    public RemoveButtonColumn getRemoveButtonColumn() {
        return removeButtonColumn;
    }

    public void setRemoveButtonColumn(RemoveButtonColumn removeButtonColumn) {
        this.removeButtonColumn = removeButtonColumn;
    }

    public CommentButtonColumn getCommentButtonColumn() {
        return commentButtonColumn;
    }

    public void setCommentButtonColumn(CommentButtonColumn commentButtonColumn) {
        this.commentButtonColumn = commentButtonColumn;
    }

    private BooleanProperty editableProperty;

    public BooleanProperty getEditableProperty() {
        return editableProperty;
    }

    public void setEditable(boolean b) {

    }

    public boolean getEditable() {
        return editableProperty.get();
    }
}
