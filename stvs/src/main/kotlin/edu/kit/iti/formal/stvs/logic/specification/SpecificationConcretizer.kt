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
package edu.kit.iti.formal.stvs.logic.specification

import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.ValidSpecification

/**
 * Interface a concretizer must implement. Concretizers create a [ConcreteSpecification]
 * (a concrete instance of a specification table) from a [ValidSpecification].
 *
 * @author Benjamin Alt
 */
interface SpecificationConcretizer {
    /**
     * Create a concrete instance from a given valid constraint specification and a list of free
     * variables.
     *
     * @param validSpecification The valid specification that should be concretized
     * @param freeVariables FreeVariables that were used in the [ValidSpecification]
     * @return calculated concrete specification
     * @throws ConcretizationException general error during concretization
     */
    @Throws(ConcretizationException::class)
    fun calculateConcreteSpecification(
        validSpecification: ValidSpecification,
        freeVariables: List<ValidFreeVariable>,
    ): ConcreteSpecification

    /**
     * Terminates the calculation of the concrete specification.
     */
    fun terminate()
}