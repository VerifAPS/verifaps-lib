package edu.kit.iti.formal.stvs.model.table;

import java.util.Optional;

/**
 * Created by philipp on 09.01.17.
 */
public class LowerBoundedInterval {
    private int lowerBound;
    private Optional<Integer> upperBound;

    public LowerBoundedInterval(int lowerBound, Optional<Integer> upperBound) {
        this.lowerBound = lowerBound;
        this.upperBound = upperBound;
    }
}
