package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
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
    private Set<CodeIoVariable> codeIoVariables;
    private Set<SpecIoVariable> specIOVariables;
    private FreeVariableSet freeVariableSet;
    private List<RowComment> rowComments;
    private Optional<ValidSpecification> validSpecification;
    private Map<String, ColumnConfig> columnConfigMap;

    // For finding SpecProblems when cells change.
    private ExpressionParser parser;
    private TypeChecker typeChecker;

    public ConstraintSpecification(ConstraintSpecification constraintSpecification) {

    }

    public ConstraintSpecification(Set<Type> typeContext, Set<CodeIoVariable> ioVariables, FreeVariableSet freeVariableSet) {
        this.typeContext = typeContext;
        this.freeVariableSet = freeVariableSet;
        // TODO
    }

    public void addProblemsListener(Consumer<List<SpecProblem>> listener) {

    }

    public void addEmptyColumn(SpecIoVariable variable) {

    }

    public SpecIoVariable getSpecIOVariableForColumn(String column) {
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
