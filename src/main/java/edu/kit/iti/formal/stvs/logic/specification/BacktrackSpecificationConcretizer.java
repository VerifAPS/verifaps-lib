package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;

import java.util.ArrayList;
import java.util.Stack;
import java.util.function.Consumer;

/**
 * Created by bal on 09.01.17.
 */
public class BacktrackSpecificationConcretizer implements SpecificationConcretizer {
    private ConcretizerContext context;
    private ConcreteSpecification concreteSpecification;
    private ConstraintSpecification constraintSpecification;
    private Stack<RowSolver> rowSolverStack;

    public BacktrackSpecificationConcretizer(ConcretizerContext context) {

    }

    public void addSuccessfulConcretizationListener(Consumer<ConcreteSpecification> listener) {

    }

    public ConcretizerContext getContext() {

        return null;
    }

    public void setContext(ConcretizerContext context) {

    }

    public void createConcreteSpecification() {

    }

    /**
     * Launch a new simulation after a specification change, unless one is already running
     * @param spec The changed spec
     */
    public void onSpecificationChanged(ConstraintSpecification spec) {

    }
}
