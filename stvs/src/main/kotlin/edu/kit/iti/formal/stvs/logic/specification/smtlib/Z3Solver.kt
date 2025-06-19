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
import edu.kit.iti.formal.stvs.logic.specification.ConcretizationException
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum
import edu.kit.iti.formal.stvs.model.expressions.ValueBool
import edu.kit.iti.formal.stvs.model.expressions.ValueInt
import edu.kit.iti.formal.stvs.model.table.ConcreteCell
import edu.kit.iti.formal.stvs.model.table.ConcreteDuration
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.SpecificationRow
import org.antlr.v4.runtime.CharStreams
import java.io.IOException
import java.util.function.Consumer
import java.util.regex.Pattern

/**
 * This class prepares a given SmtString to be solved with z3 and interprets the output.
 *
 * @author Leon Kaucher
 */
class Z3Solver(config: GlobalConfig) {
    private val timeout = config.simulationTimeout

    @JvmField
    var z3Path: String = config.z3Path
    var process: Process? = null
        private set

    /**
     * Concretizes `smtString` using Z3. After the concretization has ended a
     * [ConcreteSpecification] is returned. If the timeout is reached before the z3 process has
     * terminated, an Exception is thrown.
     *
     * @param smtString string to be solved
     * @param ioVariables list of [ValidIoVariable] used in the specification.
     * @return concretized concrete specification
     * @throws ConcretizationException general concretization problem.
     */
    @Throws(ConcretizationException::class)
    private fun concretize(smtString: String, ioVariables: List<ValidIoVariable>): ConcreteSpecification {
        val processBuilder = ProcessBuilder(z3Path, "-in", "-smt2") // TODO timeout
        try {
            val process = processBuilder.start()
            this.process = process
            process.outputStream.writer().use {
                it.write(smtString)
                it.close()
            }

            val exitValue = process.waitFor() // handles interrupts
            val z3Result = process.inputStream.bufferedReader().readText()
            val error = process.errorStream.bufferedReader().readText()

            if (Thread.currentThread().isInterrupted) {
                process.destroyForcibly()
                throw ConcretizationException("Interrupted Concretization")
            }

            if (exitValue == 0 || error.isEmpty()) {
                val expression = solverStringToSexp(z3Result)
                return buildConcreteSpecFromSExp(expression, ioVariables)
            } else {
                throw ConcretizationException("Z3 process failed. Output: \n$error")
            }
        } catch (e: IOException) {
            e.printStackTrace()
            throw ConcretizationException(e)
        }
    }

    /**
     * This method first generates a `smtString` from [SmtModel] and adds commands to tell
     * Z3 to solve the model. Then it calls [Z3Solver.concretize].
     *
     * @param smtModel constraint hat holds all information to generate a smtString
     * @param validIoVariables variables that might appear in the solver output
     * @return concretized concrete specification
     * @see Z3Solver.concretize
     * @throws ConcretizationException general concretization problem
     */
    @Throws(ConcretizationException::class)
    fun concretizeSmtModel(
        smtModel: SmtModel,
        validIoVariables: List<ValidIoVariable>
    ): ConcreteSpecification {
        val constraintString = smtModel.globalConstraintsToText()
        val headerString = smtModel.headerToText()
        val commands = "(check-sat)\n(get-model)\n(exit)"
        val z3Input = """
             $headerString
             $constraintString
             $commands
             """.trimIndent()
        return concretize(z3Input, validIoVariables)
    }

    @Throws(ConcretizationException::class)
    private fun solverStringToSexp(z3String: String): List<SList> {
        var output = SExprFacade.parse(CharStreams.fromString(z3String))

        val first = output.firstOrNull()
            ?: throw ConcretizationException("Z3 parsing failed. Given input '$z3String' is empty.")

        val firstAtom = first as? SSymbol
            ?: throw ConcretizationException("Z3 parsing failed. First Sexpr must be an atom. $first")

        if (firstAtom.toString() != "sat") {
            throw ConcretizationException("Solver returned status: Unsatisfiable")
        }

        return (output[1] as SList).filterIsInstance<SList>()
    }

    companion object {
        private val VAR_PATTERN: Pattern =
            Pattern.compile("(?<name>[\$a-zA-Z0-9_]+)_(?<row>\\d+)_(?<cycle>\\d+)")
        private val DURATION_PATTERN: Pattern = Pattern.compile("n_(?<cycleCount>\\d+)")

        /**
         * Converts a [SExpr] (already parsed output of the solver) to a
         * [ConcreteSpecification].
         *
         * @param sexpr expression that should be converted
         * @param validIoVariables variables that were used in the specification to resolve variables in
         * the solver output
         * @return converted specification
         */
        private fun buildConcreteSpecFromSExp(sexpr: List<SList>, validIoVariables: List<ValidIoVariable>): ConcreteSpecification {
            val rawDurations = extractRawDurations(sexpr)
            // convert raw durations into duration list
            val durations = buildConcreteDurations(rawDurations)
            val rawRows = extractRawRows(sexpr, durations)
            // convert raw rows into specificationRows
            val specificationRows =
                buildSpecificationRows(validIoVariables, durations, rawRows)
            return ConcreteSpecification(validIoVariables, specificationRows, durations, false)
        }

        /**
         * Creates [SpecificationRows][SpecificationRow] from raw rows.
         *
         * @param validIoVariables variables that might appear in the specification
         * @param durations list of duration for each row
         * @param rawRows Mapping from cycle number x variable name to cell expression as string
         * @return list of specification rows
         */
        private fun buildSpecificationRows(
            validIoVariables: List<ValidIoVariable>, durations: List<ConcreteDuration>,
            rawRows: Map<Int, MutableMap<String?, String>>
        ): List<SpecificationRow<ConcreteCell>> {
            val specificationRows = arrayListOf<SpecificationRow<ConcreteCell>>()
            durations.forEach { duration: ConcreteDuration ->
                buildSpecificationRow(validIoVariables, rawRows, specificationRows, duration)
            }
            return specificationRows
        }

        /**
         * Adds [SpecificationRows][SpecificationRow] to the map for one `duration`. This will
         * add a [SpecificationRow] for each cycle in the given duration. This method uses
         * `validIoVariables` to determine the [Type] of the variable and convert the cell in
         * the raw row accordingly.
         *
         * @param validIoVariables variables that might appear in the specification
         * @param rawRows Mapping from cycle number x variable name to cell expression as string
         * @param specificationRows map of specification rows (aggregator)
         * @param duration duration containing multiple cycles
         */
        private fun buildSpecificationRow(
            validIoVariables: List<ValidIoVariable>,
            rawRows: Map<Int, MutableMap<String?, String>>,
            specificationRows: MutableList<SpecificationRow<ConcreteCell>>, duration: ConcreteDuration
        ) {
            for (cycle in 0 until duration.duration) {
                val rawRow: Map<String?, String>? = rawRows[duration.beginCycle + cycle]
                val newRow = hashMapOf<String, ConcreteCell>()
                validIoVariables.forEach(
                    Consumer { validIoVariable: ValidIoVariable? ->
                    if (rawRow == null) {
                        newRow[validIoVariable!!.name] = ConcreteCell(validIoVariable.validType.generateDefaultValue())
                        return@Consumer
                    }
                    val solvedValue = rawRow[validIoVariable!!.name]
                    if (solvedValue == null) {
                        newRow[validIoVariable.name] = ConcreteCell(validIoVariable.validType.generateDefaultValue())
                        return@Consumer
                    }
                    val value = validIoVariable.validType.match(
                        { ValueInt(BitvectorUtils.intFromHex(solvedValue, true)) },
                        { if (solvedValue == "true") ValueBool.TRUE else ValueBool.FALSE },
                        { typeEnum: TypeEnum? -> typeEnum!!.values[BitvectorUtils.intFromHex(solvedValue, false)] }
                    )
                    newRow[validIoVariable.name] = ConcreteCell(value)
                }
                )
                specificationRows.add(SpecificationRow.createUnobservableRow(newRow))
            }
        }

        /**
         * Creates a list of concrete durations.
         *
         * @param rawDurations Mapping from row number to duration
         * @return list of concrete durations
         */
        private fun buildConcreteDurations(rawDurations: Map<Int, Int>): List<ConcreteDuration> {
            val durations = arrayListOf<ConcreteDuration>()
            var aggregator = 0
            for (i in 0 until rawDurations.size) {
                val duration = rawDurations[i]
                durations.add(i, ConcreteDuration(aggregator, duration!!))
                aggregator += duration
            }
            return durations
        }

        /**
         * Extracts a Mapping (cycle number x variable name to cell expression as string) from parsed
         * solver output.
         *
         * @param sexpr parsed solver output
         * @param durations concrete durations for each row
         * @return mapping
         */
        private fun extractRawRows(sexpr: List<SList>, durations: List<ConcreteDuration>): Map<Int, MutableMap<String?, String>> {
            val rawRows = HashMap<Int, MutableMap<String?, String>>()
            sexpr.forEach { addRowToMap(durations, rawRows, it) }
            return rawRows
        }

        /**
         * Adds a raw row (mapping from cycle number x variable name to cell expression as string) to the
         * map for a given assignment from the solver that has the format (define-fun VarName_row_cycle ()
         * SolverType SolverValue).
         *
         * @param durations list of concrete durations
         * @param rawRows mapping from cycle number x variable name to cell expression as string
         * @param varAssign solver assignment
         */
        private fun addRowToMap(
            durations: List<ConcreteDuration?>,
            rawRows: MutableMap<Int, MutableMap<String?, String>>, varAssign: SList
        ) {
            if (varAssign.size == 0 || varAssign[0].toString() != "define-fun") {
                return
            }
            val identifierMatcher = VAR_PATTERN.matcher(varAssign[1].toString())
            if (identifierMatcher.matches()) {
                val varName = identifierMatcher.group("name")
                val row = identifierMatcher.group("row")
                val cycle = identifierMatcher.group("cycle")
                // is variable
                val cycleCount = cycle.toInt()
                // ignore variables if iteration > n_z
                val nz = row.toInt()
                val concreteDuration = durations[nz]
                if (cycleCount >= concreteDuration!!.duration) {
                    return
                }
                val absoluteIndex = concreteDuration.beginCycle + cycleCount
                rawRows.putIfAbsent(absoluteIndex, HashMap())
                rawRows[absoluteIndex]!![varName] = varAssign[4].toString()
            }
        }

        /**
         * Extracts Durations from parsed solver output. This is the foundation for building a
         * [ConcreteSpecification]. After the concrete durations are known, variables that depend on
         * unrollings can be extracted from solver output.
         *
         * @param sexpr parsed solver output
         * @return Map from row to duration
         */
        private fun extractRawDurations(sexpr: List<SList>): Map<Int, Int> = sexpr
                .filter { isDurationLength(it) }
                .associate {
                    val cycleCount = it[1].toString().substring(2).toInt()
                    cycleCount to BitvectorUtils.intFromHex(it[4].toString(), false)
                }

        /**
         * Adds a duration from solver output to map if `varAssign` has the following format
         * (define-fun n_z () (_ BitVec 16) #xXXXX).
         *
         * @param rawDurations raw durations (mapping from ro to duration)
         * @param varAssign solver assignment
         */
        private fun isDurationLength(varAssign: SList): Boolean {
            if (varAssign.size == 0 || varAssign[0].toString() != "define-fun") {
                return false
            }
            val durationMatcher = DURATION_PATTERN.matcher(varAssign[1].toString())
            return durationMatcher.matches()
        }
    }
}