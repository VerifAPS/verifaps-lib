package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;

import java.util.Map;

/**
 * Created by philipp on 09.01.17.
 */
public class SpecificationRow<C, D> {

    private final D duration;
    private final Map<IOVariable, C> cells;

    public SpecificationRow(D duration, Map<IOVariable, C> cells) {
        this.duration = duration;
        this.cells = cells;
    }

    public C getEntryForVariable(IOVariable variable) {
        return null;
    }

    public D getDuration() {
        return duration;
    }
}
