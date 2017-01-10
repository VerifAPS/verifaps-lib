package edu.kit.iti.formal.stvs.view.spec.table.rowActions;

import edu.kit.iti.formal.stvs.view.spec.table.DurationsColumnController;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;

/**
 * Controller of column next to the table which holds add buttons for rows
 * Fires RowEvent with ADD_ROW EventType on View
 */
public class AddButtonColumnController extends RowActionColumnController{
    private AddButtonColumn view;
    private EventHandler<ActionEvent> addButtonHandler;
    AddButtonColumnController(DurationsColumnController durations) {
        super(durations);
    }
    public AddButtonColumn getView(){
        return view;
    }
}
