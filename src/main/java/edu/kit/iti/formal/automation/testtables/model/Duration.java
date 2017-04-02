package edu.kit.iti.formal.automation.testtables.model;

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

/**
 * <p>Created on 10.12.16</p>
 *
 * @author Alexander Weigl
 */
public class Duration {
    private int lower;
    private int upper;

    public Duration() {
        assert invariant();
    }

    public Duration(int l, int u) {
        lower = l;
        upper = u;
        assert invariant();
    }

    public boolean invariant() {
        return (upper >= lower || isUnbounded()) && lower >= 0;
    }

    /**
     * returns true, iff the step can be applied arbitrary often (no upper bound)
     *
     * @return
     */
    public boolean isUnbounded() {
        return upper == -1;
    }

    /**
     * returns true, iff the step is applied only once
     *
     * @return
     */
    public boolean isOneStep() {
        return fixedStep() && upper == 1;
    }

    /**
     * returns true, if the step can be overjumped directly
     *
     * @return
     */
    public boolean isSkippable() {
        return lower == 0;
    }

    /**
     * returns the maximum integer interval border.
     * <p>
     * <p>Useful for the integer width needed to store the clock value</p>
     *
     * @return
     */
    public int maxCounterValue() {
        return getBound() + 1;
    }

    /**
     * Returns true if the duration is a singleton interval
     *
     * @return
     */
    public boolean fixedStep() {
        return upper == lower;
    }

    public int getLower() {
        return lower;
    }

    public void setLower(int lower) {
        this.lower = lower;
    }

    public int getUpper() {
        return upper;
    }

    public void setUpper(int upper) {
        this.upper = upper;
    }

    /**
     * checks if the given integer lies within the duration
     *
     * @param cycles
     * @return
     */
    public boolean contains(int cycles) {
        return (lower <= cycles && (isUnbounded() || cycles <= upper));
    }

    /**
     * @return
     */
    public int getBound() {
        return isUnbounded() ? lower : upper;
    }
}
