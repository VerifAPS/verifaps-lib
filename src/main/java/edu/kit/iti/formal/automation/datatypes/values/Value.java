package edu.kit.iti.formal.automation.datatypes.values;

import edu.kit.iti.formal.automation.datatypes.Any;

/**
 * Created by weigl on 11.06.14.
 */
public interface Value<T extends Any> {
    public T getDataType();
}
