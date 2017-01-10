package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;

import java.util.Map;

/**
 * Created by philipp on 09.01.17.
 */
public class SpecificationRow<C, D> {

    private final D duration;
    private final Map<VariableIdentifier, C> cells;

    public SpecificationRow(D duration, Map<VariableIdentifier, C> cells) {
        this.duration = duration;
        this.cells = cells;
    }

    public C getEntryForVariable(VariableIdentifier variable) {
        return null;
    }

    public D getDuration() {
        return duration;
    }
}
