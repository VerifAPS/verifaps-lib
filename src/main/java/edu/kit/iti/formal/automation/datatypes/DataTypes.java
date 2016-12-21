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

import java.util.HashMap;
import java.util.Set;

/**
 * <p>DataTypes class.</p>
 *
 * @author Alexander Weigl (25.06.2014)
 * @version 1
 */
public class DataTypes {
    static HashMap<String, Any> map = new HashMap<>();

    static void add(Any any) {
        map.put(any.getName(), any);
        map.put(any.getName().replace("_", ""), any);
    }

    static {
        add(AnyBit.BOOL);
        add(AnyBit.LWORD);
        add(AnyBit.WORD);
        add(AnyBit.DWORD);

        add(AnyInt.SINT);
        add(AnyInt.INT);
        add(AnyInt.DINT);
        add(AnyInt.LINT);

        add(AnyInt.USINT);
        add(AnyInt.UINT);
        add(AnyInt.UDINT);
        add(AnyInt.ULINT);

        add(AnyReal.LREAL);
        add(AnyReal.REAL);

        add(IECString.STRING_8BIT);
        add(IECString.STRING_16BIT);

        add(TimeType.TIME_TYPE);

        add(AnyDate.DATE);
        add(AnyDate.DATE_AND_TIME);
        add(AnyDate.TIME_OF_DAY);

        map.put("TOD", AnyDate.TIME_OF_DAY);
        map.put("DT", AnyDate.DATE_AND_TIME);
        map.put("T", TimeType.TIME_TYPE);
    }

    /**
     * <p>getDataType.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public static Any getDataType(String name) {
        return map.get(name);
    }

    /**
     * <p>getDataTypeNames.</p>
     *
     * @return a {@link java.util.Set} object.
     */
    public static Set<String> getDataTypeNames() {
        return map.keySet();
    }
}
