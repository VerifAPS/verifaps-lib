package edu.kit.iti.formal.stvs.model.table.constraint;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import edu.kit.iti.formal.stvs.model.table.constraint.problems.SpecProblem;

import java.util.List;
import java.util.Set;
import java.util.function.Consumer;

/**
 * Created by philipp on 09.01.17.
 */
public class ConstraintSpecification extends SpecificationTable<ConstraintCell, ConstraintDuration> {

    private List<Consumer<List<SpecProblem>>> problemsListeners;
    private Set<Type> typeContext;

    public ConstraintSpecification(Set<Type> typeContext, Set<IOVariable> ioVariables) {
        this.typeContext = typeContext;
    }

    public void addProblemsListener(Consumer<List<SpecProblem>> listener) {

    }

    public List<SpecProblem> getProblems() {
        return null;
    }

    public Set<Type> getTypeContext() {
        return typeContext;
    }

    public void setTypeContext(Set<Type> typeContext) {
        this.typeContext = typeContext;
    }
}
