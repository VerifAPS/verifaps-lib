package edu.kit.iti.formal.stvs.view.spec.table.rowActions;

import edu.kit.iti.formal.stvs.view.spec.table.DurationsColumnController;

/**
 * This class represents a column next to the Table with additional buttons for row action (e.g. remove, add, comment)
 * The class observes changes of the DurationsColumn to create or remove buttons and binds their Y-Position to the Y-Position of the duration cell
 * so the automatically align to rows.
 */
public abstract class RowActionColumnController {
    /**
     * @param durations A controller for the DurationsColumn that should be observed
     */
    RowActionColumnController(DurationsColumnController durations) {
    }
}
