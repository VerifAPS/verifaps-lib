package edu.kit.iti.formal.automation.testtables;

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

import edu.kit.iti.formal.smv.ast.*;

/**
 * created on 15.12.16
 *
 * @author Alexander Weigl
 * @version 1
 */
public class DelayModuleBuilder implements Runnable {
    private final int historyLength;
    private final SMVType datatype;
    private final SVariable variable;
    private SMVType moduleType;
    private SMVModule module = new SMVModule();

    public DelayModuleBuilder(SVariable var, int cycles) {

        historyLength = Math.abs(cycles);
        assert historyLength > 0;
        datatype = var.getDatatype();
        variable = var;
        module.setName(String.format("History_%d_of_%s", historyLength, var.getName()));

        if (datatype == null)
            throw new IllegalArgumentException("No datatype given");

    }

    @Override
    public void run() {
        // one module parameter
        SVariable mp = new SVariable("val", datatype);
        module.getModuleParameter().add(mp);

        // state variables
        SVariable[] vars = new SVariable[historyLength + 1];
        vars[0] = mp;
        for (int i = 1; i <= historyLength; i++) {
            SVariable v = new SVariable("_$" + i, datatype);
            vars[i] = v;
            module.getStateVars().add(v);
        }

        // next($<i>) = $<i-1>
        for (int i = 1; i < vars.length; i++) {
            module.getNextAssignments().add(
                    new SAssignment(vars[i], vars[i - 1])
            );
        }

        // type
        moduleType = new SMVType.Module(module.getName(), variable);
    }

    public SMVType getModuleType() {
        return moduleType;
    }

    public DelayModuleBuilder setModuleType(SMVType moduleType) {
        this.moduleType = moduleType;
        return this;
    }

    public SMVModule getModule() {
        return module;
    }

    public DelayModuleBuilder setModule(SMVModule module) {
        this.module = module;
        return this;
    }

    public int getHistoryLength() {
        return historyLength;
    }
}
