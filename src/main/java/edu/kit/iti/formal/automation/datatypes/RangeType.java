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

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class RangeType extends Any {
    private long bottom, top;
    private AnyInt base = AnyInt.INT;

    /**
     * <p>Constructor for RangeType.</p>
     *
     * @param bottom a long.
     * @param top a long.
     * @param base a {@link edu.kit.iti.formal.automation.datatypes.AnyInt} object.
     */
    public RangeType(long bottom, long top, AnyInt base) {
        this.bottom = bottom;
        this.top = top;
    }

    /**
     * <p>Getter for the field <code>bottom</code>.</p>
     *
     * @return a long.
     */
    public long getBottom() {
        return bottom;
    }

    /**
     * <p>Setter for the field <code>bottom</code>.</p>
     *
     * @param bottom a long.
     */
    public void setBottom(long bottom) {
        this.bottom = bottom;
    }

    /**
     * <p>Getter for the field <code>top</code>.</p>
     *
     * @return a long.
     */
    public long getTop() {
        return top;
    }

    /**
     * <p>Setter for the field <code>top</code>.</p>
     *
     * @param top a long.
     */
    public void setTop(long top) {
        this.top = top;
    }

    /**
     * <p>Getter for the field <code>base</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.AnyInt} object.
     */
    public AnyInt getBase() {
        return base;
    }

    /**
     * <p>Setter for the field <code>base</code>.</p>
     *
     * @param base a {@link edu.kit.iti.formal.automation.datatypes.AnyInt} object.
     */
    public void setBase(AnyInt base) {
        this.base = base;
    }

    /** {@inheritDoc} */
    @Override
    public String repr(Object obj) {
        return base.repr(obj);
    }


    /** {@inheritDoc} */
    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
