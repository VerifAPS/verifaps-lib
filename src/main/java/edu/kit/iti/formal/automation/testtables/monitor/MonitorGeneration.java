package edu.kit.iti.formal.automation.testtables.monitor;

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.schema.IoVariable;
import edu.kit.iti.formal.automation.testtables.schema.Variable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.concurrent.Callable;

/**
 * @author Alexander Weigl
 * @version 1 (23.03.17)
 */
public class MonitorGeneration implements Callable<TopLevelElements> {
    final GeneralizedTestTable gtt;
    final FunctionBlockDeclaration fb = new FunctionBlockDeclaration();

    public MonitorGeneration(GeneralizedTestTable gtt) {
        this.gtt = gtt;
    }

    @Override public TopLevelElements call() throws Exception {
        final VariableBuilder vars = fb.getLocalScope().builder();
        vars.push(VariableDeclaration.INPUT);

        // IOVariables -> VAR_INPUT
        gtt.getIoVariables().values().forEach(v -> vars.identifiers(v.getName())
                .setBaseType(v.getDataType().value()).create());

        // VAR_OUTPUT WARNING : BOOL; END_VAR
        vars.clear().push(VariableDeclaration.OUTPUT).identifiers("WARNING")
                .setBaseType("BOOL").close();

        for (int i = 0; i < gtt.getRegion().count(); i++) {
            vars.identifiers(String.format("ROW_%2d", i)).setBaseType("BOOL").close();
        }



        return new TopLevelElements(Arrays.asList(fb));
    }
}
