package edu.kit.iti.formal.automation.testtables.concretizer;

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;

import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (22.01.17)
 */
public class ChocoConcretizer extends DefaultConcretizer {
    @Override
    public Optional<ConcreteTestTable> apply(GeneralizedTestTable generalizedTestTable) {
        askForDurationInstantiation(generalizedTestTable);

    }
}
