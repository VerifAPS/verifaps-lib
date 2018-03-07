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
import edu.kit.iti.formal.automation.datatypes.promotion.DefaultTypePromoter;
import edu.kit.iti.formal.automation.datatypes.promotion.TypePromotion;
import edu.kit.iti.formal.automation.st.ast.Copyable;

import java.io.Serializable;

/**
 * BinaryOperator represents a binary operator, e.g. addition +, multiply *, etc.
 * <p>
 * <p>Created on 24.11.16.</p>
 *
 * @author Alexander Weigl
 * @version 1
 */
public class BinaryOperator implements Operator{
    private final String symbol;
    private final AnyDt validType;

    /**
     *
     */
    protected TypePromotion promoter = new DefaultTypePromoter();

    /**
     * <p>Constructor for BinaryOperator.</p>
     *
     * @param symbol    a {@link java.lang.String} object.
     * @param validType a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     */
    protected BinaryOperator(String symbol, AnyDt validType) {
        this.symbol = symbol;
        this.validType = validType;
        Operators.register(symbol, this);
    }

    /**
     * <p>isTypeConform.</p>
     *
     * @param argument a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     * @return a boolean.
     */
    public boolean isTypeConform(AnyDt argument) {
        return argument.getClass().isAssignableFrom(validType.getClass());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String symbol() {
        return symbol;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AnyDt[] getExpectedDataTypes() {
        return new AnyDt[]{validType, validType};
    }

    /**
     * <p>getPromotedType.</p>
     *
     * @param left  a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     * @param right a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     */
    public AnyDt getPromotedType(AnyDt left, AnyDt right) {
        return promoter.getPromotion(left, right);
    }


    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        BinaryOperator that = (BinaryOperator) o;

        return symbol != null ? symbol.equals(that.symbol) : that.symbol == null;
    }

    @Override
    public int hashCode() {
        return symbol != null ? symbol.hashCode() : 0;
    }
}
