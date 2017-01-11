package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.CodeIOVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.SpecIOVariable;
import edu.kit.iti.formal.stvs.model.expressions.ExpressionParser;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeChecker;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;

/**
 * Created by philipp on 09.01.17.
 *
 */
public class ConstraintSpecification extends SpecificationTable<ConstraintCell, ConstraintDuration> {

    private List<Consumer<List<SpecProblem>>> problemsListeners;

    private Set<Type> typeContext;
    private Set<CodeIOVariable> codeIOVariables;
    private Set<SpecIOVariable> specIOVariables;
    private FreeVariableSet freeVariableSet;
    private List<RowComment> rowComments;
    private Optional<ValidSpecification> validSpecification;

    // For finding SpecProblems when cells change.
    private ExpressionParser parser;
    private TypeChecker typeChecker;

    public ConstraintSpecification(Set<Type> typeContext, Set<CodeIOVariable> ioVariables, FreeVariableSet freeVariableSet) {
        this.typeContext = typeContext;
        this.freeVariableSet = freeVariableSet;
        // TODO
    }

    public void addProblemsListener(Consumer<List<SpecProblem>> listener) {

    }

    public Type getTypeForColumn(String column) {
        return null;
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

    public FreeVariableSet getFreeVariableSet() {
        return freeVariableSet;
    }

    public List<RowComment> getRowComments() {
        return rowComments;
    }

    public void setRowComments(List<RowComment> rowComments) {
        this.rowComments = rowComments;
    }

    /**
     * @return a parsed and type-checked specification
     */
    public Optional<ValidSpecification> getValidSpecification() {
        return null;
    }
}
