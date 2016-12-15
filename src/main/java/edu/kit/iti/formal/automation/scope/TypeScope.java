package edu.kit.iti.formal.automation.scope;

import edu.kit.iti.formal.automation.datatypes.*;

import java.lang.String;
import java.util.TreeMap;

import static edu.kit.iti.formal.automation.datatypes.AnyBit.*;
import static edu.kit.iti.formal.automation.datatypes.AnyInt.*;
import static edu.kit.iti.formal.automation.datatypes.IECString.*;

/**
 * Stores the available user defined/built-in datatypes
 * Created by weigl on 24.11.16.
 */
public class TypeScope extends TreeMap<String, Any> {

    private TypeScope() {
    }

    public static TypeScope empty() {
        return new TypeScope();
    }


    public static TypeScope builtin() {
        TypeScope e = empty();
        e.register(SINT, INT, LINT, DINT);
        e.register(USINT, UINT, ULINT, UDINT);
        e.register(BOOL, BYTE, LWORD, WORD, DWORD);
        e.register(STRING_8BIT, STRING_16BIT);
        e.register(AnyDate.TIME_OF_DAY, AnyDate.DATE_AND_TIME, AnyDate.DATE,
                TimeType.TIME_TYPE);
        e.register(AnyReal.REAL, AnyReal.LREAL);
        return e;
    }

    public void register(Any... any) {
        for (Any a : any)
            put(a.getName(), a);
    }
}