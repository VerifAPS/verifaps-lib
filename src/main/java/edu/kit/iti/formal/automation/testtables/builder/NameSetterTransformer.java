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


import edu.kit.iti.formal.automation.testtables.io.Report;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.TableModule;

/**
 * Transfers the name of the table to the name of the SMV module.
 * Created by weigl on 17.12.16.
 */
public class NameSetterTransformer implements TableTransformer {
    @Override
    public void accept(TableTransformation tt) {
        TableModule mt = tt.getTableModule();
        GeneralizedTestTable gtt = tt.getTestTable();
        if (gtt.getName() == null || gtt.getName().isEmpty()) {
            Report.fatal("No table name given.");
        }
        mt.setName(gtt.getName());
    }
}
