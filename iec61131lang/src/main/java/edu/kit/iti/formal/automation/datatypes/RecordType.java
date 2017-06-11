package edu.kit.iti.formal.automation.datatypes;

/*-
 * #%L
 * iec61131lang
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

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class RecordType extends Any {
    private String name;
    private List<Field> fields = new ArrayList<>();

    /**
     * <p>Constructor for RecordType.</p>
     *
     * @param name a {@link java.lang.String} object.
     */
    public RecordType(String name) {
        this.name = name;
    }

    /**
     * <p>Getter for the field <code>fields</code>.</p>
     *
     * @return a {@link java.util.List} object.
     */
    public List<Field> getFields() {
        return fields;
    }

    /**
     * <p>addField.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @param dataType a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public void addField(String name, Any dataType) {
        fields.add(new Field(name, dataType));
    }

    /** {@inheritDoc} */
    @Override
    public String repr(Object obj) {
        return null;
    }


    public class Field {
        private String name;
        private Any dataType;
        private Object defValue;

        public Field(String name, Any dataType) {
            this.name = name;
            this.dataType = dataType;
        }

        public String getName() {
            return name;
        }

        public void setName(String name) {
            this.name = name;
        }

        public Any getDataType() {
            return dataType;
        }

        public void setDataType(Any dataType) {
            this.dataType = dataType;
        }

        public Object getDefValue() {
            return defValue;
        }

        public void setDefValue(Object defValue) {
            this.defValue = defValue;
        }

    }


    /** {@inheritDoc} */
    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
