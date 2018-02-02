/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
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
 */
package edu.kit.iti.formal.automation.testtables.model;


import edu.kit.iti.formal.automation.testtables.Facade;
import edu.kit.iti.formal.automation.testtables.io.Report;
import edu.kit.iti.formal.smv.ast.SVariable;

/**
 * Created by weigl on 15.12.16.
 */
public class SReference {
    private int cycles;
    private SVariable variable;

    public SReference(int cycles, SVariable variable) {
        if (cycles >= 0) {
            Report.fatal("Only support for negative reference (looking backwards).");
            Report.abort();
        }
        this.cycles = cycles;
        this.variable = variable;
    }

    public int getCycles() {
        return cycles;
    }

    public void setCycles(int cycles) {
        this.cycles = cycles;
    }

    public SVariable getVariable() {
        return variable;
    }

    public void setVariable(SVariable variable) {
        this.variable = variable;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        SReference that = (SReference) o;

        if (cycles != that.cycles) return false;
        return variable != null ? variable.equals(that.variable) : that.variable == null;

    }

    @Override
    public int hashCode() {
        int result = cycles;
        result = 31 * result + (variable != null ? variable.hashCode() : 0);
        return result;
    }

    /**
     * creates a reference variable
     *
     * @return
     */
    public SVariable asVariable() {
        String newName  = Facade.getHistoryName(variable, Math.abs(cycles));
        return new SVariable(newName, getVariable().getSMVType());
    }


}
