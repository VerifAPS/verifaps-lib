package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.model.common.ValidIoVariable
import edu.kit.iti.formal.stvs.model.expressions.Expression
import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem
import javafx.util.Callback

/**
 * A specification table that has been validated (is free from [SpecProblem]s) and can be
 * concretized (by a [edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer]).
 *
 * @author Benjamin Alt
 */
class ValidSpecification : SpecificationTable<ValidIoVariable, Expression, LowerBoundedInterval>(
    Callback { _: ValidIoVariable? -> arrayOf() },
    Callback { _: LowerBoundedInterval? -> arrayOf() })
