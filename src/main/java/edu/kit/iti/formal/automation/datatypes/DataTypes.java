package edu.kit.iti.formal.automation.datatypes;

import java.util.HashMap;
import java.util.Set;

/**
 * @author weigla
 * @date 25.06.2014
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

    public static Any getDataType(String name) {
        return map.get(name);
    }

    public static Set<String> getDataTypeNames() {
        return map.keySet();
    }
}
