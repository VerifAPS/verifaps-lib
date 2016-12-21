package edu.kit.iti.formal.automation.testtables.model.options;

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

import java.util.HashMap;

/**
 * Created by weigl on 16.12.16.
 */
public class TableOptions {

    @Property
    private Mode mode;

    @Property(namespace = "concrete-table")
    private ConcreteTableOptions concreteTableOptions = new ConcreteTableOptions();

    @Property(namespace = "datatype")
    private DataTypeOptions dataTypeOptions = new DataTypeOptions();

    public Mode getMode() {
        if (mode != null)
            mode = Mode.CONFORMANCE;
        return mode;
    }

    public TableOptions setMode(Mode mode) {
        this.mode = mode;
        return this;
    }

    public ConcreteTableOptions getConcreteTableOptions() {
        return concreteTableOptions;
    }

    public TableOptions setConcreteTableOptions(ConcreteTableOptions concreteTableOptions) {
        this.concreteTableOptions = concreteTableOptions;
        return this;
    }

    public DataTypeOptions getDataTypeOptions() {
        return dataTypeOptions;
    }

    public TableOptions setDataTypeOptions(DataTypeOptions dataTypeOptions) {
        this.dataTypeOptions = dataTypeOptions;
        return this;
    }
}
