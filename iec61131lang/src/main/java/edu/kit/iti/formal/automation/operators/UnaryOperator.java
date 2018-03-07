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

import edu.kit.iti.formal.automation.datatypes.AnyDt;
import edu.kit.iti.formal.automation.datatypes.AnyUnsignedInt;

/**
 * <p>UnaryOperator class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class UnaryOperator implements Operator {
    private final String symbol;
    private final AnyDt validFor;

    /**
     * <p>Constructor for UnaryOperator.</p>
     *
     * @param symbol a {@link java.lang.String} object.
     * @param any a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     */
    public UnaryOperator(String symbol, AnyDt any) {
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
    public AnyDt[] getExpectedDataTypes() {
        return new AnyDt[]{validFor};
    }

    public boolean isValid(AnyDt a) {
        return validFor.getClass().isAssignableFrom(a.getClass());
    }

    public AnyDt getPromotedType(AnyDt a) {
        if (isValid(a)) {
            if (a instanceof AnyUnsignedInt) {
                AnyUnsignedInt anyUnsignedInt = (AnyUnsignedInt) a;
                return anyUnsignedInt.asSigned();
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
