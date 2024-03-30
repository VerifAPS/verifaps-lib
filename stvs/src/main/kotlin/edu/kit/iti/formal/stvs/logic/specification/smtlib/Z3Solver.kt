package edu.kit.iti.formal.stvs.logic.specification.smtlib

import de.tudresden.inf.lat.jsexp.Sexp
import de.tudresden.inf.lat.jsexp.SexpFactory
import de.tudresden.inf.lat.jsexp.SexpParserException
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
import java.io.*
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
        val processBuilder = ProcessBuilder(z3Path, "-in", "-smt2") //TODO timeout
        try {
            val process = processBuilder.start()
            this.process = process
            process.outputStream.writer().use {
                it.write(smtString)
            }

            var exitValue = process.waitFor() // handles interrupts
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
        } catch (e: SexpParserException) {
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
        smtModel: SmtModel?,
        validIoVariables: List<ValidIoVariable>
    ): ConcreteSpecification {
        val constraintString = smtModel!!.globalConstraintsToText()
        val headerString = smtModel.headerToText()
        val commands = "(check-sat)\n(get-model)\n(exit)"
        val z3Input = """
             $headerString
             $constraintString
             $commands
             """.trimIndent()
        return concretize(z3Input, validIoVariables)
    }

    @Throws(ConcretizationException::class, SexpParserException::class)
    private fun solverStringToSexp(z3String: String): Sexp {
        var z3 = z3String
        if (!z3.startsWith("sat")) {
            throw ConcretizationException("Solver returned status: Unsatisfiable")
        }
        z3 = z3.substring(z3.indexOf('\n') + 1)
        return SexpFactory.parse(z3)
    }

    companion object {
        private val VAR_PATTERN: Pattern = Pattern.compile("(?<name>[\$a-zA-Z0-9_]+)_(?<row>\\d+)_(?<cycle>\\d+)")
        private val DURATION_PATTERN: Pattern = Pattern.compile("n_(?<cycleCount>\\d+)")

        /**
         * Converts a [Sexp] (already parsed output of the solver) to a
         * [ConcreteSpecification].
         *
         * @param sexpr expression that should be converted
         * @param validIoVariables variables that were used in the specification to resolve variables in
         * the solver output
         * @return converted specification
         */
        private fun buildConcreteSpecFromSExp(sexpr: Sexp, validIoVariables: List<ValidIoVariable>)
                : ConcreteSpecification {
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
                validIoVariables.forEach(Consumer { validIoVariable: ValidIoVariable? ->
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
                        { typeEnum: TypeEnum? -> typeEnum!!.values[BitvectorUtils.intFromHex(solvedValue, false)] })
                    newRow[validIoVariable.name] = ConcreteCell(value!!)
                })
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
        private fun extractRawRows(
            sexpr: Sexp,
            durations: List<ConcreteDuration?>
        ): Map<Int, MutableMap<String?, String>> {
            val rawRows: MutableMap<Int, MutableMap<String?, String>> = HashMap()
            sexpr.forEach(Consumer { varAssign: Sexp -> addRowToMap(durations, rawRows, varAssign) })
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
            rawRows: MutableMap<Int, MutableMap<String?, String>>, varAssign: Sexp
        ) {
            if (varAssign.length == 0 || varAssign[0].toIndentedString() != "define-fun") {
                return
            }
            val identifierMatcher = VAR_PATTERN.matcher(varAssign[1].toIndentedString())
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
                rawRows[absoluteIndex]!![varName] = varAssign[4].toIndentedString()
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
        private fun extractRawDurations(sexpr: Sexp): Map<Int, Int> {
            val rawDurations: MutableMap<Int, Int> = HashMap()
            sexpr.forEach(Consumer { varAssign: Sexp -> addDurationToMap(rawDurations, varAssign) })
            return rawDurations
        }

        /**
         * Adds a duration from solver output to map if `varAssign` has the following format
         * (define-fun n_z () (_ BitVec 16) #xXXXX).
         *
         * @param rawDurations raw durations (mapping from ro to duration)
         * @param varAssign solver assignment
         */
        private fun addDurationToMap(rawDurations: MutableMap<Int, Int>, varAssign: Sexp) {
            if (varAssign.length == 0 || varAssign[0].toIndentedString() != "define-fun") {
                return
            }
            val durationMatcher = DURATION_PATTERN.matcher(varAssign[1].toIndentedString())
            if (durationMatcher.matches()) {
                // is duration
                val cycleCount = durationMatcher.group("cycleCount").toInt()
                rawDurations[cycleCount] = BitvectorUtils.intFromHex(varAssign[4].toIndentedString(), false)
            }
        }
    }
}
