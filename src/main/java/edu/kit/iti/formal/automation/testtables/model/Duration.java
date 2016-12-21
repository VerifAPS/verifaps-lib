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
 * Created by weigl on 10.12.16.
 */
public class Duration {
    public int lower;
    public int upper;

    public Duration() {
    }

    public Duration(int l, int u) {
        lower = l;
        upper = u;
    }

    public boolean isUnbounded() {
        return upper == -1;
    }

    public boolean isOneStep() {
        return fixedStep() && upper == 1;
    }

    public boolean skipable() {
        return lower == 0;
    }

    public int maxCounterValue() {
        return Math.max(lower, upper) + 1;
    }

    public boolean fixedStep() {
        return upper == lower;
    }

    public int getLower() {
        return lower;
    }

    public int getUpper() {
        return upper;
    }
}
