package edu.kit.iti.formal.automation.operators;

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

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyUInt;

/**
 * <p>UnaryOperator class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class UnaryOperator implements Operator {
    private final String symbol;
    private final Any validFor;

    /**
     * <p>Constructor for UnaryOperator.</p>
     *
     * @param symbol a {@link java.lang.String} object.
     * @param any a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public UnaryOperator(String symbol, Any any) {
        this.symbol = symbol;
        this.validFor = any;
        Operators.register(symbol, this);
    }

    /** {@inheritDoc} */
    @Override
    public String symbol() {
        return this.symbol;
    }

    /** {@inheritDoc} */
    @Override
    public Any[] getExpectedDataTypes() {
        return new Any[]{validFor};
    }

    /**
     * <p>isValid.</p>
     *
     * @param a a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     * @return a boolean.
     */
    public boolean isValid(Any a) {
        return validFor.getClass().isAssignableFrom(a.getClass());
    }

    /**
     * <p>getPromotedType.</p>
     *
     * @param a a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public Any getPromotedType(Any a) {
        if (isValid(a)) {
            if (a instanceof AnyUInt) {
                AnyUInt anyUInt = (AnyUInt) a;
                return anyUInt.asSigned();
            }
            return a;
        }
        return null;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        UnaryOperator that = (UnaryOperator) o;

        return symbol != null ? symbol.equals(that.symbol) : that.symbol == null;
    }

    @Override
    public int hashCode() {
        return symbol != null ? symbol.hashCode() : 0;
    }
}
