package edu.kit.iti.formal.automation.testtables.builder;

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

import edu.kit.iti.formal.automation.testtables.model.State;
import edu.kit.iti.formal.automation.testtables.model.options.ConcreteTableOptions;
import edu.kit.iti.formal.smv.ast.SLiteral;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.List;

/**
 * Created by weigl on 17.12.16.
 */
public class ConcreteTableInvariantTransformer implements TableTransformer {
    @Override
    public void accept(TableTransformation tt) {
        ConcreteTableOptions cto = tt.getTestTable().getOptions().getConcreteTableOptions();
        List<State> rows = tt.getTestTable().getRegion().flat();
        SMVExpr invarant = SLiteral.TRUE;

        for (int i = 0; i < rows.size(); i++) {
            int id = rows.get(i).getId();
            int count = cto.getCount(id, 1);
            SVariable clock = tt.getTableModule().getStateVar("clock" + id);
            // I = I /\ c_i = 0dX_<count>
            invarant = invarant.and(clock.equal(new SLiteral(clock.getSMVType(), count)));
        }
        invarant = invarant.not();
        tt.getTableModule().getInvarSpec().add(invarant);
    }
}
