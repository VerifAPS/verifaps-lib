package edu.kit.iti.formal.stvs.logic.specification.smtlib

import de.tudresden.inf.lat.jsexp.Sexp
import de.tudresden.inf.lat.jsexp.SexpFactory
import edu.kit.iti.formal.stvs.logic.specification.ConcretizationException
import sun.misc.IOUtils
import java.io.BufferedReader
import java.io.InputStreamReader
import java.util.*
import java.util.concurrent.TimeUnit
import java.util.regex.Pattern

class Z3SolverInteractiveInterface(
        val timeout: Long = 10,
        val z3Command: Array<String> = arrayOf("z3", "-in", "-smt2")) {
    var process: Process? = null

    fun start(): Process {
        val processBuilder = ProcessBuilder(*z3Command)
        var p = processBuilder.start()
        process = p
        return p
    }

    fun send(smt: String) {
        val process = process ?: start()
        process.outputStream.bufferedWriter().use {
            it.write(smt)
            it.flush()
        }
    }

    private fun readResponse() {
        SexpFactory.parse()
        val reader = BufferedReader(InputStreamReader(process?.inputStream, "utf-8"))
        var line: String
        val z3Result = StringBuilder("")
        while ((line = reader.readLine()) != null && !Thread.currentThread().isInterrupted) z3Result.append(line + "\n")
        reader.close()
        val error = IOUtils.toString(process.errorStream, "utf-8")
        if (Thread.currentThread().isInterrupted) {
            process.destroyForcibly()
            throw ConcretizationException("Interrupted Concretization")
        }
    }

    private fun quit() {
        send("(quit)")
        process?.waitFor(timeout, TimeUnit.SECONDS)
        try {
            val exitValue = process.waitFor()
            if (exitValue == 0 || error.length == 0) {
                val expression = solverStringToSexp(z3Result.toString())
                return buildConcreteSpecFromSExp(expression, ioVariables)
            } else {
                throw ConcretizationException("Z3 process failed. Output: \n$error")
            }
        } catch (e: InterruptedException) {
            throw ConcretizationException("Interrupted Concretization")
        }
    }

    companion object {
        private val VAR_PATTERN = Pattern.compile("(?<name>[\$a-zA-Z0-9_]+)_(?<row>\\d+)_(?<cycle>\\d+)")
        private val DURATION_PATTERN = Pattern.compile("n_(?<cycleCount>\\d+)")
        /**
         * Converts a [Sexp] (already parsed output of the solver) to a
         * [ConcreteSpecification].
         *
         * @param sexpr expression that should be converted
         * @param validIoVariables variables that were used in the specification to resolve variables in
         * the solver output
         * @return converted specification
         */
        private fun buildConcreteSpecFromSExp(sexpr: Sexp,
                                              validIoVariables: List<ValidIoVariable>): ConcreteSpecification {
            val rawDurations = extractRawDurations(sexpr)
            // convert raw durations into duration list
            val durations = buildConcreteDurations(rawDurations)
            val rawRows = extractRawRows(sexpr, durations)
            // convert raw rows into specificationRows
            val specificationRows = buildSpecificationRows(validIoVariables, durations, rawRows)
            return ConcreteSpecification(validIoVariables, specificationRows, durations, false)
        }

        /**
         * Creates [SpecificationRows][SpecificationRow] from raw rows.
         *
         * @param validIoVariables variables that might appear in the specification
         * @param durations list of duration for each row
         * @param rawRows Mapping from cycle number x variable name to cell expression as text
         * @return list of specification rows
         */
        private fun buildSpecificationRows(
                validIoVariables: List<ValidIoVariable>, durations: List<ConcreteDuration>,
                rawRows: Map<Int, Map<String, String>>): List<SpecificationRow<ConcreteCell>> {
            val specificationRows = ArrayList<SpecificationRow<ConcreteCell>>()
            durations.forEach { duration -> buildSpecificationRow(validIoVariables, rawRows, specificationRows, duration) }
            return specificationRows
        }

        /**
         * Adds [SpecificationRows][SpecificationRow] to the map for one `duration`. This will
         * add a [SpecificationRow] for each cycle in the given duration. This method uses
         * `validIoVariables` to determine the [Type] of the variable and convert the cell in
         * the raw row accordingly.
         *
         * @param validIoVariables variables that might appear in the specification
         * @param rawRows Mapping from cycle number x variable name to cell expression as text
         * @param specificationRows map of specification rows (aggregator)
         * @param duration duration containing multiple cycles
         */
        private fun buildSpecificationRow(validIoVariables: List<ValidIoVariable>,
                                          rawRows: Map<Int, Map<String, String>>,
                                          specificationRows: MutableList<SpecificationRow<ConcreteCell>>, duration: ConcreteDuration) {
            for (cycle in 0 until duration.getDuration()) {
                val rawRow = rawRows[duration.getBeginCycle() + cycle]
                val newRow = HashMap<String, ConcreteCell>()
                validIoVariables.forEach { validIoVariable ->
                    if (rawRow == null) {
                        newRow[validIoVariable.getName()] = ConcreteCell(validIoVariable.getValidType().generateDefaultValue())
                        return@validIoVariables.forEach
                    }
                    val solvedValue = rawRow!![validIoVariable.getName()]
                    if (solvedValue == null) {
                        newRow[validIoVariable.getName()] = ConcreteCell(validIoVariable.getValidType().generateDefaultValue())
                        return@validIoVariables.forEach
                    }
                    val value = validIoVariable.getValidType().match(
                            { ValueInt(BitvectorUtils.intFromHex(solvedValue, true)) },
                            { if (solvedValue == "true") ValueBool.TRUE else ValueBool.FALSE },
                            { typeEnum -> typeEnum.getValues().get(BitvectorUtils.intFromHex(solvedValue, false)) })
                    newRow[validIoVariable.getName()] = ConcreteCell(value)
                }
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
            val durations = ArrayList<ConcreteDuration>()
            var aggregator = 0
            for (i in 0 until rawDurations.size) {
                val duration = rawDurations[i]
                durations.add(i, ConcreteDuration(aggregator, duration))
                aggregator += duration!!
            }
            return durations
        }

        /**
         * Extracts a Mapping (cycle number x variable name to cell expression as text) from parsed
         * solver output.
         *
         * @param sexpr parsed solver output
         * @param durations concrete durations for each row
         * @return mapping
         */
        private fun extractRawRows(sexpr: Sexp,
                                   durations: List<ConcreteDuration>): Map<Int, Map<String, String>> {
            val rawRows = HashMap<Int, Map<String, String>>()
            sexpr.forEach { varAssign -> addRowToMap(durations, rawRows, varAssign) }
            return rawRows
        }

        /**
         * Adds a raw row (mapping from cycle number x variable name to cell expression as text) to the
         * map for a given assignment from the solver that has the format (define-fun VarName_row_cycle ()
         * SolverType SolverValue).
         *
         * @param durations list of concrete durations
         * @param rawRows mapping from cycle number x variable name to cell expression as text
         * @param varAssign solver assignment
         */
        private fun addRowToMap(durations: List<ConcreteDuration>,
                                rawRows: MutableMap<Int, Map<String, String>>, varAssign: Sexp) {
            if (varAssign.length == 0 || varAssign.get(0).toIndentedString() != "define-fun") {
                return
            }
            val identifierMatcher = VAR_PATTERN.matcher(varAssign.get(1).toIndentedString())
            if (identifierMatcher.matches()) {
                val varName = identifierMatcher.group("name")
                val row = identifierMatcher.group("row")
                val cycle = identifierMatcher.group("cycle")
                // is variable
                val cycleCount = Integer.parseInt(cycle)
                // ignore variables if iteration > n_z
                val nz = Integer.parseInt(row)
                val concreteDuration = durations[nz]
                if (cycleCount >= concreteDuration.getDuration()) {
                    return
                }
                val absoluteIndex = concreteDuration.getBeginCycle() + cycleCount
                (rawRows as java.util.Map<Int, Map<String, String>>).putIfAbsent(absoluteIndex, HashMap())
                rawRows[absoluteIndex].put(varName, varAssign.get(4).toIndentedString())
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
            val rawDurations = HashMap<Int, Int>()
            sexpr.forEach { varAssign -> addDurationToMap(rawDurations, varAssign) }
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
            if (varAssign.length == 0 || varAssign.get(0).toIndentedString() != "define-fun") {
                return
            }
            val durationMatcher = DURATION_PATTERN.matcher(varAssign.get(1).toIndentedString())
            if (durationMatcher.matches()) {
                // is duration
                val cycleCount = Integer.parseInt(durationMatcher.group("cycleCount"))
                rawDurations[cycleCount] = BitvectorUtils.intFromHex(varAssign.get(4).toIndentedString(), false)
            }
        }
    }
}
