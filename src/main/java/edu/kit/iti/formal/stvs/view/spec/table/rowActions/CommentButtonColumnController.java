package edu.kit.iti.formal.stvs.view.spec.table.rowActions;

import edu.kit.iti.formal.stvs.view.spec.table.DurationsColumnController;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;

/**
 * Controller of column next to the table which holds comment buttons for rows
 * Fires RowEvent with COMMENT_ROW EventType on View
 */
public class CommentButtonColumnController extends RowActionColumnController{
    private CommentButtonColumn view;
    private EventHandler<ActionEvent> commentButtonHandler;
    CommentButtonColumnController(DurationsColumnController durations) {
        super(durations);
    }
    public CommentButtonColumn getView(){
        return view;
    }
}
