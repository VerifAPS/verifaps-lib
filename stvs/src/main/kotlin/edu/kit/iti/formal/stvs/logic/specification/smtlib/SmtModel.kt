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
package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.automation.analysis.toHuman
import edu.kit.iti.formal.smt.SExpr
import edu.kit.iti.formal.smt.SList

/**
 * Represents sets of constraints and definitions.
 *
 * @author Carsten Csiky
 */
data class SmtModel(
    val globalConstraints: MutableList<SExpr> = arrayListOf(),
    val variableDefinitions: MutableList<SExpr> = arrayListOf(),
) {
    /**
     * Adds all constraints and definitions of `other` to this object.
     *
     * @param other object from which the constraints/definitions should be taken
     * @return this (now with added constraints/definitions)
     */
    fun combine(other: SmtModel): SmtModel {
        globalConstraints.addAll(other.globalConstraints)
        variableDefinitions.addAll(other.variableDefinitions)
        return this
    }

    fun toSexpr(): List<SExpr> {
        val seq = ArrayList(variableDefinitions)

        globalConstraints.forEach {
            seq.add(SList("assert", it))
        }
        return seq
    }

    /**
     * Converts all definitions to text compatible with smt definitions.
     *
     * @return definitions as string
     */
    fun headerToText(): String = distinctVariableDefinitions.joinToString("\n") {
        it.toHuman()
    }

    /**
     * Converts all global constraints to text compatible with smt.
     *
     * @return constraints as string
     */
    fun globalConstraintsToText(): String = globalConstraints
        .joinToString(" \n ") { SList("assert", it).toString() }

    fun toText(): String = "${headerToText()}\n${globalConstraintsToText()}"

    fun addGlobalConstraint(c: SExpr): SmtModel {
        this.globalConstraints.add(c)
        return this
    }

    fun addHeaderDefinition(c: SExpr): SmtModel {
        this.variableDefinitions.add(c)
        return this
    }

    val distinctVariableDefinitions: Set<SExpr>
        get() = LinkedHashSet(variableDefinitions)
}