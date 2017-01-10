package edu.kit.iti.formal.stvs.view.spec.table.cells;

import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.table.constraint.ConstraintCell;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.StringProperty;

public class ValueCellController implements Controller {
    private ValueCell valueCell;
    /**
     * Listens if model cell changes
     */
    private void onAddUserInputStringChanged(String string){}
    private StringProperty value;

    public ValueCellController(ConstraintCell constraintCell) {
    }

    @Override
    public ValueCell getView() {
        return valueCell;
    }
}
