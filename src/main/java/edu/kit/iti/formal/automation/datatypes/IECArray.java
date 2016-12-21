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

import edu.kit.iti.formal.automation.st.ast.Range;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 07/10/14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class IECArray extends Any {
    private final Any fieldType;
    private List<Range> ranges = new ArrayList<>();

    /**
     * <p>Constructor for IECArray.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @param fieldType a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     * @param ranges a {@link java.util.List} object.
     */
    public IECArray(String name, Any fieldType, List<Range> ranges) {
        this.name = name;
        this.fieldType = fieldType;
        this.ranges = ranges;
    }

    /**
     * <p>Getter for the field <code>fieldType</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public Any getFieldType() {
        return fieldType;
    }

    /**
     * <p>Getter for the field <code>ranges</code>.</p>
     *
     * @return a {@link java.util.List} object.
     */
    public List<Range> getRanges() {
        return ranges;
    }

    /**
     * <p>Setter for the field <code>ranges</code>.</p>
     *
     * @param ranges a {@link java.util.List} object.
     */
    public void setRanges(List<Range> ranges) {
        this.ranges = ranges;
    }

    /** {@inheritDoc} */
    @Override
    public String repr(Object obj) {
        return null;
    }


    /** {@inheritDoc} */
    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
