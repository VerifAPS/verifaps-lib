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

import edu.kit.iti.formal.smt.SExpr
import edu.kit.iti.formal.smt.SExprFacade
import edu.kit.iti.formal.smt.SList
import edu.kit.iti.formal.smt.SSymbol
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable
import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.table.ValidSpecification
import java.util.stream.Collectors
import java.util.stream.IntStream
import kotlin.math.min

/**
 * Created by csicar on 09.02.17.
 *
 * @author Carsten Csiky
 */
class SmtEncoder(
    private val maxDurations: List<Int>,
    private val specification: ValidSpecification,
    private val validFreeVariables: List<ValidFreeVariable>,
) {
    // Map<Row, Max. number of cycles for that row>
    private val ioVariables: List<ValidIoVariable>
    private val freeVariablesContext: Map<String, Type>
    private val ioVariableTypes: List<String?>

    var constraint: SmtModel

    /**
     * Creates an encoder for a specification. Each row is unrolled at most maxDuration times. This is
     * a helper constructor if one do not want to specify a maximum duration for each row.
     *
     * @param maxDuration        Max duration for all rows
     * @param specification      The specification that should be encoded
     * @param validFreeVariables The free variables that are referred to in `specification`
     */
    constructor(
        maxDuration: Int,
        specification: ValidSpecification,
        validFreeVariables: List<ValidFreeVariable>,
    ) : this(
        generateAllSameList(maxDuration, specification.rows.size),
        specification,
        validFreeVariables,
    )

    /**
     * Creates an encoder for a specification. Each row is unrolled at most the number specified in
     * `maxDurations`.
     *
     * @param maxDurations       list of maximum durations for each row
     * @param specification      specification to encode
     * @param validFreeVariables free variables that appear in the specification
     */
    init {
        require(maxDurations.size == specification.rows.size) {
            "Size of maxDurations and size of specification rows do not match"
        }
        ioVariables = specification.columnHeaders
        freeVariablesContext = validFreeVariables.associate { it.name to it.type }
        ioVariableTypes = ioVariables.map { it.name }

        constraint = SmtModel().apply {
            variableDefinitions.addAll(createFreeVariables())
            variableDefinitions.addAll(setFreeVariablesDefaultValues())
        }

        // Step (2): upper und lower Bound von Durations festlegen
        defineDurationBounds()

        // Step (5)
        unrollRowsToConstraints()

        // Step 4 neg. Indizes verbinden
        connectBackwardReferences()
    }

    /**
     * This connects backward references by aggregating all possible backward references relative to
     * the row before they appeared.
     */
    private fun connectBackwardReferences() {
        for (ioVariable in ioVariables) {
            val column = specification.getColumnByName(ioVariable.name)
            val variableName = ioVariable.name
            // Iterate over Rows
            for (z in column.cells.indices) {
                column.cells[z]
                // Add n_x to const declaration
                constraint.addHeaderDefinition(
                    SList("declare-const", sym("n_$z"), TYPE_BV_16),
                )
                // Iterate over potential backward steps
                for (i in 1..getMaxDurationSum(z - 1)) {
                    // Iterate over possible cycles in last row
                    for (k in 0..getMaxDuration(z - 1)) {
                        // n_(z-1) = k => A_z_i = A_(z-1)_(k-i)
                        constraint.addGlobalConstraint(
                            SList(
                                "implies",
                                SList(
                                    "=",
                                    sym("n_${z - 1}"),
                                    BitvectorUtils.hexFromInt(k, 4),
                                ),
                                SList(
                                    "=",
                                    sym("|${variableName}_${z}_${-i}|"),
                                    sym("|${variableName}_${z - 1}_${k - i}|"),
                                ),
                            ),
                        )
                        // Add backward reference to const declaration
                        constraint.addHeaderDefinition(
                            SList(
                                "declare-const",
                                sym("|${variableName}_${z - 1}_${k - i}|"),
                                getSmtLibVariableTypeName(ioVariable.validType),
                            ),
                        )
                    }
                    // Add backward reference to const declaration
                    constraint.addHeaderDefinition(
                        SList(
                            "declare-const",
                            sym("|${variableName}_${z}_${-i}|"),
                            getSmtLibVariableTypeName(ioVariable.validType),
                        ),
                    )
                }
            }
        }
    }

    /**
     * Unrolls constraints (expressions are converted to constraints for each cell) to their duration
     * specified in `maxDurations`.
     */
    private fun unrollRowsToConstraints() {
        for (ioVariable in ioVariables) {
            val column = specification.getColumnByName(ioVariable.name)
            for (z in column.cells.indices) {
                val expression = column.cells[z]

                for (i in 0 until getMaxDuration(z)) {
                    val visitor = SmtConvertExpressionVisitor(
                        this,
                        z,
                        i,
                        ioVariable,
                    )
                    val expressionConstraint = expression.accept(visitor)
                    // n_z >= i => ExpressionVisitor(z,i,...)
                    this.constraint = SmtModel(
                        visitor.constraint.globalConstraints,
                        visitor.constraint.variableDefinitions,
                    )
                        .combine(this.constraint)
                    constraint.addGlobalConstraint(
                        SList(
                            "implies",
                            SList("bvuge", sym("n_$z"), BitvectorUtils.hexFromInt(i, 4)),
                            expressionConstraint,
                        ),
                    )
                }
            }
        }
    }

    /**
     * Adds global constraint to limit durations to their bounds. n_z is limited to [x,y] where x is
     * determined by [LowerBoundedInterval.lowerBound] for each row and y is determined by
     * [LowerBoundedInterval.upperBound] or the entry `maxDurations` whichever one is
     * less.
     */
    private fun defineDurationBounds() {
        for (z in specification.durations.indices) {
            val interval = specification.durations.get(z)!!
            // n_z >= lowerBound_z
            constraint.addGlobalConstraint(
                SList(
                    "bvuge",
                    sym("n_$z"),
                    BitvectorUtils.hexFromInt(interval.lowerBound, 4),
                ),
            )
            // n_z <= upperBound_z
            if (interval.upperBound != null) {
                constraint.addGlobalConstraint(
                    SList(
                        "bvule",
                        sym("n_$z"),
                        BitvectorUtils.hexFromInt(
                            min(
                                interval.upperBound.toDouble(),
                                getMaxDuration(z).toDouble(),
                            ).toInt(),
                            4,
                        ),
                    ),
                )
            } else {
                constraint.addGlobalConstraint(
                    SList(
                        "bvule",
                        sym("n_$z"),
                        BitvectorUtils.hexFromInt(getMaxDuration(z), 4),
                    ),
                )
            }
        }
    }

    /**
     * Generates an expression for the solver of the form (= (variable defaultValue)) for a given
     * variable.
     *
     * @param variable variable for which the assertion should be generated
     * @return asserts that the variable is equal to its default value
     */
    private fun getDefaultValueEquality(variable: ValidFreeVariable): SExpr {
        val constraint = variable.constraint

        val scev = SmtConvertExpressionVisitor(
            this,
            0,
            0,
            variable.asIOVariable(),
        )
        return constraint!!.accept(scev)

        /*return defaultValue.match((integerVal) -> sexpr("=",
                        "|" + variable.getName() + "|",
                        BitvectorUtils.hexFromInt(integerVal, 4)),
                (boolVal) -> sexpr("=", "|" + variable.getName() + "|",
                        boolVal ? "true" : "false"),
                enumVal -> sexpr("=", "|" + variable.getName() + "|",
                        BitvectorUtils.hexFromInt(
                                enumVal.getType().getValues().indexOf(enumVal),
                                4)));*/
    }

    fun isIoVariable(name: String?): Boolean = ioVariableTypes.contains(name)

    private fun setFreeVariablesDefaultValues(): List<SExpr> = validFreeVariables
        .filter { variable: ValidFreeVariable -> variable.constraint != null }
        .map { variable: ValidFreeVariable -> this.getDefaultValueEquality(variable) }
        .map { SList("assert", it) }

    fun getTypeForVariable(variableName: String?): Type? {
        var type = freeVariablesContext[variableName]
        if (type == null) {
            type = try {
                specification.getColumnHeaderByName(variableName).validType
            } catch (_: NoSuchElementException) {
                null
            }
        }
        return type
    }

    private fun createFreeVariables(): List<SExpr> = freeVariablesContext.entries.stream()
        .filter { item: Map.Entry<String?, Type> -> !isIoVariable(item.key) }
        .map { item: Map.Entry<String?, Type> ->
            getDeclarationForVariable(
                item.value,
                item.key!!,
            )
        }.collect(Collectors.toList())

    private fun getMaxDurationSum(z: Int): Int {
        var sum = 0
        for (i in 0..z) {
            sum += getMaxDuration(i)
        }

        return sum
    }

    private fun getMaxDuration(j: Int): Int {
        if (j < 0) {
            return 0
        }
        val interval = specification.durations[j]!!.upperBound

        return if (interval != null) {
            min(maxDurations[j].toDouble(), interval.toDouble()).toInt()
        } else {
            maxDurations[j]
        }
    }

    companion object {
        /**
         * Generates a List with one number repeated multiple times
         *
         * @param number number to be repeated
         * @param times  how many times `number` should be repeated
         * @return List of number repeated `times` times.
         */
        private fun generateAllSameList(number: Int, times: Int): List<Int> =
            IntStream.generate { number }.limit(times.toLong()).boxed()
                .collect(Collectors.toList())

        private fun getDeclarationForVariable(type: Type, variableName: String) =
            SList("declare-const", SSymbol(variableName), getSmtLibVariableTypeName(type))

        fun getSmtLibVariableTypeName(type: Type) = when (type) {
            is TypeBool -> TYPE_BOOL
            is TypeInt -> TYPE_BV_16
            is TypeEnum -> TYPE_BV_16
        }
    }
}

val TYPE_BV_16 = SExprFacade.parseExpr("(_ BitVec 16)")
val TYPE_BOOL = SSymbol("Bool")

fun sym(s: String) = SSymbol(s)