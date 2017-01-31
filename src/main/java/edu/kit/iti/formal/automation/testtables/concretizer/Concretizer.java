package edu.kit.iti.formal.automation.testtables.concretizer;

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;

import java.util.Optional;
import java.util.function.Function;

/**
 * @author Alexander Weigl
 * @version 1 (22.01.17)
 */
public interface Concretizer extends Function<GeneralizedTestTable,
        Optional<ConcreteTestTable>> {
}
