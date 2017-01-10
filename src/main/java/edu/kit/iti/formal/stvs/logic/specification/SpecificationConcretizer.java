package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.table.concrete.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.constraint.ConstraintSpecification;

import java.util.ArrayList;
import java.util.Stack;
import java.util.function.Consumer;

/**
 * Created by bal on 09.01.17.
 */
public class SpecificationConcretizer {
    private ConcretizerContext context;
    private ConcreteSpecification concreteSpecification;
    private ConstraintSpecification constraintSpecification;
    private Stack<RowSolver> rowSolverStack;

    public SpecificationConcretizer(ConcretizerContext context) {

    }

    public void addSuccessfulConcretizationListener(Consumer<ConcreteSpecification> listener) {

    }

    public void onIOVariablesChange(ArrayList<IOVariable> changedIOVariables) {

    }

    public ConcretizerContext getContext() {

        return null;
    }

    public ConcreteSpecification getConcreteSpecification() {

        return null;
    }

    public void onSpecificationChanged(ConstraintSpecification spec) {

    }
}
