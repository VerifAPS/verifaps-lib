package edu.kit.iti.formal.stvs.view.spec.table.rowActions;

import edu.kit.iti.formal.stvs.view.spec.table.DurationsColumnController;
import edu.kit.iti.formal.stvs.view.spec.table.cells.HybridCellController;
import javafx.collections.ListChangeListener;
import javafx.scene.Node;

import java.util.function.Consumer;

/**
 * This class represents a column next to the Table with additional buttons for row action (e.g. remove, add, comment)
 * The class observes changes of the DurationsColumn to create or remove buttons and binds their Y-Position to the Y-Position of the duration cell
 * so the automatically align to rows.
 */
public abstract class RowActionColumnController {
    /**
     * @param durations A controller for the DurationsColumn that should be observed
     */

    public RowActionColumnController(DurationsColumnController durations) {
        /*
        durations.getCells().addListener(
                (ListChangeListener.Change<? extends HybridCellController> c) -> {
                    c.getAddedSubList().forEach(this::addButton);
                    c.getRemoved().forEach(this::removeButton);
                }
        );
        */
    }

    public abstract void removeButton(int row);

    public abstract void addButton(int row, HybridCellController cell);

    public abstract Node getView();
}
