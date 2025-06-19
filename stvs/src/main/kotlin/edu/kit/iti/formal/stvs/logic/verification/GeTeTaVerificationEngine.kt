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
package edu.kit.iti.formal.stvs.logic.verification

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.algorithms.MultiModelGluer
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.automation.visitors.findFirstProgram
import edu.kit.iti.formal.smv.CounterExample
import edu.kit.iti.formal.smv.NuXMVOutput
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.code.ParsedCode
import edu.kit.iti.formal.stvs.model.common.*
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.expressions.parser.computeEnumValuesByName
import edu.kit.iti.formal.stvs.model.table.*
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator
import edu.kit.iti.formal.stvs.model.verification.Counterexample
import edu.kit.iti.formal.stvs.model.verification.VerificationError
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario
import edu.kit.iti.formal.stvs.model.verification.VerificationSuccess
import edu.kit.iti.formal.stvs.util.ProcessCreationException
import javafx.application.Platform
import javafx.beans.property.SimpleListProperty
import org.antlr.v4.runtime.CharStreams
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import tornadofx.asObservable
import java.io.File
import java.io.FileNotFoundException
import java.io.IOException
import java.util.concurrent.Callable
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.TimeoutException

/**
 * Handles communication with the GeTeTa verification engine.
 *
 * @author Benjamin Alt
 */
class GeTeTaVerificationEngine(val config: GlobalConfig, val code: ParsedCode) : VerificationEngine() {
    private var drawAutomaton: Boolean = false
    private var disableSimplify: Boolean = false
    private var getetaProcess: Process?

    /**
     * Creates an instance based on given [GlobalConfig] and `typeContext`. The
     * `typeContext` is used later for importing the possible counterexample.
     *
     * @param config config that should be used
     * @param typeContext list of types used for importing counterexample
     * @throws FileNotFoundException nuXmv not found
     */
    init {
        getetaProcess = null
        /* Check if nuXmv executable exists */
        val nuxmvFile = File(config.nuxmvFilename)
        // TODO check if nuXmv is executable by running it.
    }

    /**
     * Exports the given [VerificationScenario] to temporary files and starts the GeTeTa
     * verification engine process.
     *
     * @param scenario scenario that hold the code to be checked
     * @param spec specification that should be checked
     * @throws IOException exception while creating process
     * @throws ExportException exception while exporting
     */
    @Throws(IOException::class, ExportException::class, ProcessCreationException::class)
    override fun startVerification(scenario: VerificationScenario, spec: ConstraintSpecification) {
        val (pous, _) = IEC61131Facade.fileResolve(CharStreams.fromString(scenario.code.sourcecode), true)

        val code = pous.findFirstProgram() ?: error("No program found")
        val (_, modCode) = SymbExFacade.evaluateProgramWithLineMap(code, disableSimplify)
        val superEnumType = GetetaFacade.createSuperEnum(listOf(code.scope))

        val (freeVars, validTT) = spec.validate(this.code.definedVariables, this.code.definedTypes)

        val gtt: GeneralizedTestTable = validTT.asGtt(freeVars)

        val tt = GetetaFacade.constructSMV(gtt, superEnumType)

        if (drawAutomaton) {
            // Getata.drawAutomaton(gtt, tt)
        }

        val modTable = tt.tableModule
        val mainModule = MultiModelGluer().apply {
            val pn = gtt.programRuns.first() // only one run in geteta
            addProgramRun(pn, modCode)
            addTable("_" + tt.testTable.name, tt.ttType!!)
        }
        val modules = arrayListOf(mainModule.product, modCode, modTable)
        modules.addAll(tt.helperModules)

        val folder = File.createTempFile("gtt_", ".smv").absolutePath

        val process =
            GetetaFacade.createNuXMVProcess(
                folder,
                modules,
                config.nuxmvFilename,
                VerificationTechnique.IC3,
            )

        val op = process.outputParser
        var output = ""
        process.outputParser = {
            output = it
            op(it)
        }

        val executor = Executors.newSingleThreadScheduledExecutor()
        val future = executor.submit(process as Callable<NuXMVOutput>)

        try {
            val b = future.get(config.verificationTimeout, TimeUnit.SECONDS)

            val result =
                when (b) {
                    NuXMVOutput.Verified -> {
                        VerificationSuccess(output)
                    }

                    is NuXMVOutput.Error -> {
                        b.errors
                        VerificationError(VerificationError.Reason.VERIFICATION_LAUNCH_ERROR, output)
                    }

                    is NuXMVOutput.Cex -> {
                        b.counterExample
                        Counterexample(
                            spec,
                            b.counterExample.asConcreteSpecification(validTT),
                            output,
                        )
                    }
                }

            Platform.runLater { verificationResultProperty.set(result) }

            if (b is NuXMVOutput.Cex) {
                /*if (cexAnalysation.cexPrinter) useCounterExamplePrinter(outputFolder, b, tt, lineMap, code)
            else info("Use `--cexout' to print a cex analysation.")

            if (cexAnalysation.cexJson) useCounterExamplePrinterJson(outputFolder, b, tt)
            else info("Use `--cexjson' to print a cex analysation as json.")

            if (cexAnalysation.runAnalyzer) createRowMapping(b, tt)
            else info("Use `--row-map' to print possible row mappings.")*/
            }
            // exitProcess(errorLevel)
        } catch (e: TimeoutException) {
            cancelVerification()
        }
    }

    override fun cancelVerification() {
        if (getetaProcess != null) {
            getetaProcess!!.destroyForcibly()
            getetaProcess = null
        }
    }

    companion object {
        private val LOGGER: Logger = LoggerFactory.getLogger(GeTeTaVerificationEngine::class.java)
    }

    private fun ConstraintSpecification.validate(
        codeIoVariables: List<CodeIoVariable>,
        typeContext: List<Type>,
    ): Pair<List<ValidFreeVariable>, ValidSpecification> {
        val tc = SimpleListProperty(typeContext.asObservable())
        val freeVariableListValidator = FreeVariableListValidator(tc, freeVariableList)
        val freeVariables: List<ValidFreeVariable> = freeVariableListValidator.validFreeVariables
        val validator = ConstraintSpecificationValidator(
            tc,
            SimpleListProperty(codeIoVariables.asObservable()),
            freeVariables.asObservable(),
            this,
        )

        // TODO throw exception
        validator.problems.map { it?.errorMessage }.forEach { println(it) }
        return freeVariables to validator.validSpecification!!
    }

    val enumValues by lazy { computeEnumValuesByName(this.code.definedTypes) }

    private fun CounterExample.asConcreteSpecification(origin: ValidSpecification): ConcreteSpecification {
        val ioVars = origin.columnHeaders.toMutableList()
        val durations = List(this.states.size) { idx -> ConcreteDuration(idx, 1) }
        val rows = this.states.map {
            SpecificationRow.createUnobservableRow(
                it.map { (k, v) -> k to ConcreteCell(v.nxAsValue()) }.toMap(),
            )
        }
        return ConcreteSpecification(ioVars, rows, durations, true)
    }

    private val INT_VALUE_PATTERN = "-?0[su]d(\\d+)_([0-9]+)".toRegex()

    /**
     * From nuxmv to value
     */
    private fun String.nxAsValue(): Value {
        if (this == "TRUE") return ValueBool.TRUE
        if (this == "FALSE") return ValueBool.FALSE
        val matcher = INT_VALUE_PATTERN.matchEntire(this)
        if (matcher != null) {
            val (_, radix, v) = matcher.groupValues
            var intVal = v.toInt(radix.toInt())
            if (this[0] == '-') {
                intVal = -intVal
            }
            return ValueInt(intVal)
        }
        if (this in enumValues) {
            return enumValues[this]!!
        }
        error("Could not find type for value $this")
    }

    private fun ValidSpecification.asGtt(freeVars: List<ValidFreeVariable>): GeneralizedTestTable {
        val columnVars = this.columnHeaders.map { it.asColumnVariable() as ColumnVariable }.toMutableList()
        val cvars = columnVars.associateBy { it.name }
        val gtt = GeneralizedTestTable(
            name = this.name,
            programVariables = columnVars,
            constraintVariables = freeVars.map { it.asConstraintVariable() }.toMutableList(),
            region = Region(
                "0",
                rows.mapIndexed { idx, it -> it.asTableNode(idx + 1, cvars, durations[idx]!!) }.toMutableList(),
            ),
        )

        return gtt
    }

    private fun SpecificationRow<Expression>.asTableNode(
        id: Int,
        columnVars: Map<String, ColumnVariable>,
        duration: LowerBoundedInterval,
    ): TableNode = TableRow(id).also {
        this.cells.forEach { (t, u) ->
            val v = columnVars[t]!!
            it.rawFields[v] = GetetaFacade.parseCell(u.asString ?: "TRUE").cell()
            it.duration = duration.asDuration()
        }
    }

    private fun LowerBoundedInterval.asDuration(): Duration = GetetaFacade.parseDuration(toString())

    private fun ValidFreeVariable.asConstraintVariable() = ConstraintVariable(
        name,
        type.asDT(),
        type.asSmvType(),
        GetetaFacade.parseCell(this.constraint.toString()).cell(),
    )

    private fun ValidIoVariable.asColumnVariable() =
        ProgramVariable(name, validType.asDT(), validType.asSmvType(), role.asCCategory())

    private fun VariableRole.asCCategory() = when (this) {
        VariableRole.ASSUME -> ColumnCategory.ASSUME
        VariableRole.ASSERT -> ColumnCategory.ASSERT
    }

    private fun Type.asSmvType() = when (this) {
        is TypeInt -> SMVTypes.signed(16)
        is TypeBool -> SMVTypes.BOOLEAN
        else -> SMVTypes.GENERIC_ENUM
    }

    private fun Type.asDT(): AnyDt = when (this) {
        is TypeInt -> INT
        is TypeBool -> AnyBit.BOOL
        else -> EnumerateType("super")
    }
}