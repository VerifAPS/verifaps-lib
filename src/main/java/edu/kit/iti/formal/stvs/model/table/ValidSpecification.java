package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.SpecIOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;

import java.util.Map;
import java.util.Set;

/**
 * Created by csicar on 11.01.17.
 */
public class ValidSpecification extends SpecificationTable<Expression, LowerBoundedInterval> {

    private final Set<Type> typeContext;
    private Set<SpecIOVariable> specIOVariables;
    private FreeVariableSet freeVariableSet;


    public ValidSpecification(Set<Type> typeContext) {
        this.typeContext = typeContext;
    }
}
