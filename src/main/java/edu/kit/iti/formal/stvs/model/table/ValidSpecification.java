package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.expressions.Expression;
import edu.kit.iti.formal.stvs.model.expressions.Type;

import java.util.Map;
import java.util.Set;

/**
 * Created by csicar on 11.01.17.
 */
public class ValidSpecification extends SpecificationTable<Expression, LowerBoundedInterval> {

    private final Set<Type> typeContext;

    public ValidSpecification(Set<Type> typeContext) {
        this.typeContext = typeContext;
    }
}
