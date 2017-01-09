package edu.kit.iti.formal.stvs.view.spec.table.rowActions;

import edu.kit.iti.formal.stvs.view.spec.table.DurationsColumnController;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;

/**
 * Controller of column next to the table which holds remove buttons for rows
 * Fires RowEvent with REMOVE_ROW EventType on View
 */
public class RemoveButtonColumnController extends RowActionColumnController{
    private EventHandler<ActionEvent> removeButtonHandler;
    private RemoveButtonColumn view;

    RemoveButtonColumnController(DurationsColumnController durations) {
        super(durations);
    }

    public RemoveButtonColumn getView(){
        return view;
    }
}
