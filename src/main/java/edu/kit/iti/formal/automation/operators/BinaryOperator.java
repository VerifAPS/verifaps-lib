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
import edu.kit.iti.formal.automation.datatypes.promotion.DefaultTypePromoter;
import edu.kit.iti.formal.automation.datatypes.promotion.TypePromotion;

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class BinaryOperator implements Operator {
    final String symbol;
    final Any validType;
    protected TypePromotion promoter = new DefaultTypePromoter();

    /**
     * <p>Constructor for BinaryOperator.</p>
     *
     * @param symbol a {@link java.lang.String} object.
     * @param validType a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    protected BinaryOperator(String symbol, Any validType) {
        this.symbol = symbol;
        this.validType = validType;
        Operators.register(symbol, this);
    }

    /**
     * <p>isTypeConform.</p>
     *
     * @param argument a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     * @return a boolean.
     */
    public boolean isTypeConform(Any argument) {
        return argument.getClass().isAssignableFrom(validType.getClass());
    }

    /** {@inheritDoc} */
    @Override
    public String symbol() {
        return symbol;
    }

    /** {@inheritDoc} */
    @Override
    public Any[] getExpectedDataTypes() {
        return new Any[]{validType, validType};
    }

    /**
     * <p>getPromotedType.</p>
     *
     * @param left a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     * @param right a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public Any getPromotedType(Any left, Any right) {
        return promoter.getPromotion(left, right);
    }

}
