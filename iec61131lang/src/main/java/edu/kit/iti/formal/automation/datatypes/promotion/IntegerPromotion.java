package edu.kit.iti.formal.automation.datatypes.promotion;

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
import edu.kit.iti.formal.automation.datatypes.AnySignedInt;
import edu.kit.iti.formal.automation.datatypes.AnyUInt;

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class IntegerPromotion implements TypePromotion {
    /** Constant <code>INSTANCE</code> */
    public static final IntegerPromotion INSTANCE = new IntegerPromotion();

    /** {@inheritDoc} */
    @Override
    public Any getPromotion(Any a, Any b) {
        try {
            return promote((AnySignedInt) a, (AnySignedInt) b);
        } catch (ClassCastException e) {
            try {
                return promote((AnyUInt) a, (AnyUInt) b);
            } catch (ClassCastException e1) {
                try {
                    return promote((AnySignedInt) a, (AnyUInt) b);
                } catch (ClassCastException e2) {
                    try{
                        return promote((AnySignedInt) b, (AnyUInt) a);
                    }catch (ClassCastException e3) {
                        return null;
                    }
                }
            }
        }
    }

    /**
     * <p>promote.</p>
     *
     * @param a a {@link edu.kit.iti.formal.automation.datatypes.AnySignedInt} object.
     * @param b a {@link edu.kit.iti.formal.automation.datatypes.AnySignedInt} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public Any promote(AnySignedInt a, AnySignedInt b) {
        if (a.getBitLength() >= b.getBitLength())
            return a;
        else
            return b;
    }


    /**
     * <p>promote.</p>
     *
     * @param a a {@link edu.kit.iti.formal.automation.datatypes.AnyUInt} object.
     * @param b a {@link edu.kit.iti.formal.automation.datatypes.AnyUInt} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public Any promote(AnyUInt a, AnyUInt b) {
        if (a.getBitLength() >= b.getBitLength())
            return a;
        else
            return b;
    }

    /**
     * <p>promote.</p>
     *
     * @param a a {@link edu.kit.iti.formal.automation.datatypes.AnySignedInt} object.
     * @param b a {@link edu.kit.iti.formal.automation.datatypes.AnyUInt} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public Any promote(AnySignedInt a, AnyUInt b) {
        if (a.getBitLength() > b.getBitLength())
            return a;
        else
            return b.asSigned();
    }
}
