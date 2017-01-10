package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.common.IOVariable;

import java.util.ArrayList;

/**
 * Created by bal on 09.01.17.
 */
public class SpecificationConcretizer {
    private ConcretizerContext context;
    private ConcreteSpecification concreteSpecification;
    private ConstraintSpecification constraintSpecification;

    public SpecificationConcretizer(ConcretizerContext context) {

    }

    public void addSuccessfulConcretizationListener(Consumer<ConcreteSpecification> listener) {

    }

    public void onIOVariablesChange(ArrayList<IOVariable> changedIOVariables) {

    }

    public ConcretizerContext getContext() {

    }

    public ConcreteSpecification getConcreteSpecification() {

    }

    public void onSpecificationChanged(ConstraintSpecification spec) {

    }
}
