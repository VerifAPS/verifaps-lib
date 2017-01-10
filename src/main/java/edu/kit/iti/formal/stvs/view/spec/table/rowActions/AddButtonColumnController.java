package edu.kit.iti.formal.stvs.view.spec.table.rowActions;

import edu.kit.iti.formal.stvs.view.spec.table.DurationsColumnController;
import edu.kit.iti.formal.stvs.view.spec.table.cells.HybridCellController;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.control.Button;

/**
 * Controller of column next to the table which holds add buttons for rows
 * Fires RowEvent with ADD_ROW EventType on View
 */
public class AddButtonColumnController extends RowActionColumnController{
    private AddButtonColumn view;
    public AddButtonColumnController(DurationsColumnController durations) {
        super(durations);
    }

    @Override
    public void removeButton(int row) {

    }

    @Override
    public void addButton(int row, HybridCellController cell) {
        getView().getChildren().addAll(new Button());

    }

    public AddButtonColumn getView(){
        return view;
    }
}
