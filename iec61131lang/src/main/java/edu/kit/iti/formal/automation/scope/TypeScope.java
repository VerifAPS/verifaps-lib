package edu.kit.iti.formal.automation.scope;

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

import edu.kit.iti.formal.automation.datatypes.*;

import java.util.TreeMap;

import static edu.kit.iti.formal.automation.datatypes.AnyBit.*;
import static edu.kit.iti.formal.automation.datatypes.IECString.STRING_16BIT;
import static edu.kit.iti.formal.automation.datatypes.IECString.STRING_8BIT;

/**
 * Stores the available user defined/built-in datatypes
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class TypeScope extends TreeMap<String, Any> {

    private TypeScope() {
    }

    /**
     * <p>empty.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.scope.TypeScope} object.
     */
    public static TypeScope empty() {
        return new TypeScope();
    }

    /**
     * <p>builtin.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.scope.TypeScope} object.
     */
    public static TypeScope builtin() {
        TypeScope e = empty();
        e.register(DataTypes.SINT, DataTypes.INT, DataTypes.LINT, DataTypes.DINT);
        e.register(DataTypes.USINT, DataTypes.UINT, DataTypes.ULINT, DataTypes.UDINT);
        e.register(BOOL, BYTE, LWORD, WORD, DWORD);
        e.register(STRING_8BIT, STRING_16BIT);
        e.register(AnyDate.TIME_OF_DAY, AnyDate.DATE_AND_TIME, AnyDate.DATE,
                TimeType.TIME_TYPE);
        e.register(AnyReal.REAL, AnyReal.LREAL);
        e.register("VOID", null);
        return e;
    }

    /**
     * <p>register.</p>
     *
     * @param any a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public void register(Any... any) {
        for (Any a : any)
            put(a.getName(), a);
    }

    public void register(String name, Any type) {
        put(name, type);
    }

    public TypeScope clone() {
        TypeScope ts = new TypeScope();
        ts.putAll(this);
        return ts;
    }
}
