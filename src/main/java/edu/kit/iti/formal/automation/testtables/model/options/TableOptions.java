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

/**
 * Created by weigl on 16.12.16.
 */
public class TableOptions {
    private Mode mode;

    private ConcreteTableOptions concreteTableOptions = new ConcreteTableOptions();

    private DataTypeOptions dataTypeOptions = new DataTypeOptions();
    private boolean useNext = true;

    @Property
    public Mode getMode() {
        if (mode == null)
            mode = Mode.CONFORMANCE;
        return mode;
    }

    public void setMode(Mode mode) {
        this.mode = mode;
    }

    @Property(value = "cycles")
    public ConcreteTableOptions getConcreteTableOptions() {
        return concreteTableOptions;
    }

    public void setConcreteTableOptions(ConcreteTableOptions concreteTableOptions) {
        this.concreteTableOptions = concreteTableOptions;
    }

    @Property(value = "datatype")
    public DataTypeOptions getDataTypeOptions() {
        return dataTypeOptions;
    }

    public void setDataTypeOptions(DataTypeOptions dataTypeOptions) {
        this.dataTypeOptions = dataTypeOptions;
    }

    @Property("usenext")
    public boolean isUseNext() {
        return useNext;
    }

    public void setUseNext(boolean useNext) {
        this.useNext = useNext;
    }
}
