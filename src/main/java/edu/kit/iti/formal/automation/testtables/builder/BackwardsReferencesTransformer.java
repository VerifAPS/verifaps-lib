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
package edu.kit.iti.formal.automation.testtables.builder;


import edu.kit.iti.formal.automation.testtables.DelayModuleBuilder;
import edu.kit.iti.formal.automation.testtables.Facade;
import edu.kit.iti.formal.smv.ast.SVariable;

/**
 *
 * @author Alexander Weigl
 * @version 1 (17.12.16)
 */
public class BackwardsReferencesTransformer implements TableTransformer {
    private TableTransformation tt;

    @Override
    public void accept(TableTransformation tt) {
        this.tt = tt;
        tt.getTestTable().getReferences().forEach(this::addDelayModule);
    }

    private void addDelayModule(SVariable variable, Integer history) {
        DelayModuleBuilder b = new DelayModuleBuilder(variable, history);
        b.run();
        //Add Var
        SVariable var = new SVariable(Facade.getHistoryName(variable),
                b.getModuleType());
        tt.getTableModule().getStateVars().add(var);

        //add helper module
        tt.getHelperModules().add(b.getModule());
    }
}
