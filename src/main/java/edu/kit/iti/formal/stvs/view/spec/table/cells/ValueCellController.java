package edu.kit.iti.formal.stvs.view.spec.table.cells;

import edu.kit.iti.formal.stvs.model.table.constraint.ConstraintCell;
import javafx.beans.property.StringProperty;

import java.util.function.Consumer;

public class ValueCellController {
    /**
     * Listens if model cell changes
     */
    private Consumer<String> userInputStringListener;
    private StringProperty value;
    public ValueCellController(ConstraintCell constraintCell){
    }
}
