package edu.kit.iti.formal.automation.smv.translators;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.values.Value;

/**
 * @author Alexander Weigl
 * @version 1 (16.10.17)
 */
public interface InitValueTranslator {
    <T extends Any,S> Value<T,S> getInit(Any type);
}
