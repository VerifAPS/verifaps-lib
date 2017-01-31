package edu.kit.iti.formal.automation.testtables.concretizer;

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;

import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (22.01.17)
 */
public class ConcretizerFacade {
    private static Optional<ConcreteTestTable> concrete(Concretizer concretizer, GeneralizedTestTable gtt) {
        return concretizer.apply(gtt);
    }

    public static Optional<ConcreteTestTable> concretizeWithSMT(GeneralizedTestTable gtt) {
        SMTConcretizer smt = new SMTConcretizer();
        return concrete(smt, gtt);
    }

    public static Optional<ConcreteTestTable> concretizeWithChoco(GeneralizedTestTable gtt) {
        return concrete(new ChocoConcretizer(), gtt);
    }
}
