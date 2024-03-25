package edu.kit.iti.formal.stvs.logic.specification.smtlib

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
    private val validFreeVariables: List<ValidFreeVariable>
) {
    // Map<Row, Max. number of cycles for that row>
    private val ioVariables: List<ValidIoVariable>
    private val freeVariablesContext: Map<String, Type>
    private val ioVariableTypes: List<String?>

    var constraint: SmtModel?
        private set

    /**
     * Creates an encoder for a specification. Each row is unrolled at most maxDuration times. This is
     * a helper constructor if one do not want to specify a maximum duration for each row.
     *
     * @param maxDuration        Max duration for all rows
     * @param specification      The specification that should be encoded
     * @param validFreeVariables The free variables that are referred to in `specification`
     */
    constructor(
        maxDuration: Int, specification: ValidSpecification?,
        validFreeVariables: List<ValidFreeVariable>
    ) : this(
        generateAllSameList(maxDuration, specification!!.rows.size),
        specification, validFreeVariables
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
        require(maxDurations.size == specification.rows.size) { "Size of maxDurations and size of specification rows do not match" }
        this.ioVariables = specification.columnHeaders
        this.freeVariablesContext = validFreeVariables.associate { it.name to it.type }
        this.ioVariableTypes = ioVariables.map { it.name }

        this.constraint = SmtModel()
            .addHeaderDefinitions(createFreeVariables())
            .addHeaderDefinitions(setFreeVariablesDefaultValues())

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
                val expression = column.cells[z]
                // Add n_x to const declaration
                constraint!!.addHeaderDefinitions(
                    SList.sexpr("declare-const", "n_$z", "(_ BitVec 16)")
                )
                // Iterate over potential backward steps
                for (i in 1..getMaxDurationSum(z - 1)) {
                    // Iterate over possible cycles in last row
                    for (k in 0..getMaxDuration(z - 1)) {
                        // n_(z-1) = k => A_z_i = A_(z-1)_(k-i)
                        constraint!!.addGlobalConstrains(
                            SList.sexpr(
                                "implies",
                                SList.sexpr(
                                    "=", "n_" + (z - 1),
                                    BitvectorUtils.hexFromInt(k, 4)
                                ),
                                SList.sexpr(
                                    "=", "|" + variableName + "_" + z + "_"
                                            + (-i) + "|",
                                    "|" + variableName + "_" + (z - 1) + "_"
                                            + (k - i) + "|"
                                )
                            )
                        )
                        // Add backward reference to const declaration
                        constraint!!.addHeaderDefinitions(
                            SList.sexpr(
                                "declare-const",
                                "|" + variableName + "_" + (z - 1) + "_"
                                        + (k - i) + "|",
                                getSmtLibVariableTypeName(
                                    ioVariable.validType
                                )
                            )
                        )
                    }
                    // Add backward reference to const declaration
                    constraint!!.addHeaderDefinitions(
                        SList.sexpr(
                            "declare-const",
                            "|" + variableName + "_" + z + "_" + (-i) + "|",
                            getSmtLibVariableTypeName(
                                ioVariable.validType
                            )
                        )
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
                val expression = column.cells[z]!!

                for (i in 0 until getMaxDuration(z)) {
                    val visitor = SmtConvertExpressionVisitor(
                        this, z, i, ioVariable
                    )
                    val expressionConstraint = expression.takeVisitor(visitor)
                    // n_z >= i => ExpressionVisitor(z,i,...)
                    this.constraint = SmtModel(
                        visitor.constraint.globalConstraints,
                        visitor.constraint.variableDefinitions
                    )
                        .combine(this.constraint)
                    constraint!!.addGlobalConstrains(
                        SList.sexpr(
                            "implies",
                            SList.sexpr(
                                "bvuge", "n_$z",
                                BitvectorUtils.hexFromInt(i, 4)
                            ),
                            expressionConstraint
                        )
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
            constraint!!.addGlobalConstrains(
                SList.sexpr(
                    "bvuge", "n_$z",
                    BitvectorUtils.hexFromInt(interval.lowerBound, 4)
                            + ""
                )
            )
            // n_z <= upperBound_z
            if (interval.upperBound.isPresent) {
                constraint!!.addGlobalConstrains(
                    SList.sexpr(
                        "bvule", "n_$z",
                        BitvectorUtils.hexFromInt(
                            min(
                                interval.upperBound.get().toDouble(),
                                getMaxDuration(z).toDouble()
                            ).toInt(), 4
                        )
                    )
                )
            } else {
                constraint!!.addGlobalConstrains(
                    SList.sexpr(
                        "bvule", "n_$z",
                        BitvectorUtils.hexFromInt(getMaxDuration(z), 4)
                    )
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
    private fun getDefaultValueEquality(variable: ValidFreeVariable): SExpression {
        val constraint = variable.constraint

        val scev = SmtConvertExpressionVisitor(
            this,
            0, 0, variable.asIOVariable()
        )
        return constraint!!.takeVisitor(scev)

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

    fun isIoVariable(name: String?): Boolean {
        return ioVariableTypes.contains(name)
    }

    private fun setFreeVariablesDefaultValues(): List<SExpression> {
        return validFreeVariables
            .filter { variable: ValidFreeVariable -> variable.constraint != null }
            .map { variable: ValidFreeVariable -> this.getDefaultValueEquality(variable) }
            .map { SList.sexpr("assert", it) }
    }

    fun getTypeForVariable(variableName: String?): Type? {
        var type = freeVariablesContext[variableName]
        if (type == null) {
            type = try {
                specification.getColumnHeaderByName(variableName).validType
            } catch (exception: NoSuchElementException) {
                null
            }
        }
        return type
    }

    private fun createFreeVariables(): List<SExpression> {
        return freeVariablesContext.entries.stream()
            .filter { item: Map.Entry<String?, Type> -> !isIoVariable(item.key) }
            .map { item: Map.Entry<String?, Type> ->
                getDeclarationForVariable(
                    item.value,
                    item.key!!
                )
            }.collect(Collectors.toList())
    }

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

        return if (interval.isPresent) {
            min(maxDurations[j].toDouble(), interval.get().toDouble()).toInt()
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
        private fun generateAllSameList(number: Int, times: Int): List<Int> {
            return IntStream.generate { number }.limit(times.toLong()).boxed()
                .collect(Collectors.toList())
        }

        private fun getDeclarationForVariable(type: Type, variableName: String) =
            SList.sexpr("declare-const", "|$variableName|", getSmtLibVariableTypeName(type))

        fun getSmtLibVariableTypeName(type: Type) = when (type) {
            is TypeInt -> "(_ BitVec 16)"
            is TypeBool -> "Bool"
            is TypeEnum -> "(_ BitVec 16)"
        }
    }
}
