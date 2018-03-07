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

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class TableTypePromotion implements TypePromotion {
    private List<AnyDt[]> table = new ArrayList<>();

    /**
     * <p>Constructor for TableTypePromotion.</p>
     */
    public TableTypePromotion() {
    }

    /**
     * <p>Constructor for TableTypePromotion.</p>
     *
     * @param table a {@link java.util.List} object.
     */
    public TableTypePromotion(List<AnyDt[]> table) {
        this.table = table;
    }

    /**
     * <p>getDefault.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.promotion.TableTypePromotion} object.
     */
    public static TableTypePromotion getDefault() {
        TableTypePromotion t = new TableTypePromotion();
        return t;
    }

    /** {@inheritDoc} */
    @Override
    public AnyDt getPromotion(AnyDt a, AnyDt b) {
        for (AnyDt[] ary : table) {
            if (ary[0].equals(a) && ary[1].equals(b))
                return ary[2];
        }
        return null;
    }
}
