package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;
import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;

import java.util.Map;
import java.util.Set;

/**
 * Created by csicar on 11.01.17.
 */
public class ValidSpecification extends SpecificationTable<Expression, LowerBoundedInterval> {

    private final Set<Type> typeContext;
    private final Map<VariableIdentifier, Type> columnTypes;

    public ValidSpecification(Set<Type> typeContext, Map<VariableIdentifier, Type> columnTypes) {
        this.typeContext = typeContext;
        this.columnTypes = columnTypes;
    }
}
