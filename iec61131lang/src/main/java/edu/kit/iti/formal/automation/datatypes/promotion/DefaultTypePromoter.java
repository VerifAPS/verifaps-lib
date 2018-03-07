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

import edu.kit.iti.formal.automation.datatypes.AnyDt;

import java.io.Serializable;
import java.util.ArrayList;

/**
 * Type Promotion based on a table.
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class DefaultTypePromoter implements TypePromotion, Serializable {
    ArrayList<TypePromotion> promoters = new ArrayList<>();

    /**
     * <p>Constructor for DefaultTypePromoter.</p>
     */
    public DefaultTypePromoter() {
        promoters.add(IntegerPromotion.INSTANCE);
        promoters.add(BitPromotion.INSTANCE);
        promoters.add(RealPromotion.INSTANCE);
        promoters.add(SelfPromotion.INSTANCE);
    }

    /** {@inheritDoc} */
    @Override
    public AnyDt getPromotion(AnyDt a, AnyDt b) {
        for (TypePromotion tp : promoters) {
            AnyDt c = tp.getPromotion(a, b);
            if (c != null) return c;
        }
        return null;
    }
}
