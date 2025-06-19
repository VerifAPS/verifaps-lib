/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
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
class ValidSpecification :
    SpecificationTable<ValidIoVariable, Expression, LowerBoundedInterval>(
        Callback { _: ValidIoVariable? -> arrayOf() },
        Callback { _: LowerBoundedInterval? -> arrayOf() },
    )