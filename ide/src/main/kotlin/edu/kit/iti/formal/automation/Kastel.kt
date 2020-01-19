package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor
import edu.kit.iti.formal.automation.st.util.UsageFinder
import edu.kit.iti.formal.automation.st0.MultiCodeTransformation
import edu.kit.iti.formal.automation.st0.TransformationState
import edu.kit.iti.formal.automation.st0.trans.CodeTransformation
import edu.kit.iti.formal.automation.st0.trans.RealToInt
import edu.kit.iti.formal.automation.st0.trans.STCodeTransformation
import edu.kit.iti.formal.automation.visitors.Utils
import edu.kit.iti.formal.smv.*
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.info

import java.io.File
import java.math.BigInteger

/**
 *
 * @author Alexander Weigl
 * @version 1 (10.07.18)
 */
object KastelDemonstrator {
    val FOLDER = File("/home/weigl/Documents/Kastel/Industry4.0/Demonstrator2018")
    val INPUT_FILE = File(FOLDER, "VerificationSubject.st")
    val INPUT_FIX_FILE = File(FOLDER, "VerificationSubjectFix.st")

    @JvmStatic
    fun main(args: Array<String>) {
        SINT.bitLength = 10; INT.bitLength = 10; DINT.bitLength = 10;LINT.bitLength = 10
        USINT.bitLength = 10; UINT.bitLength = 10;UDINT.bitLength = 10; ULINT.bitLength = 10
        runInfoPipeline(INPUT_FILE, prefix="if_%d.smv")
        runInfoPipeline(INPUT_FIX_FILE, prefix="fix_%d.smv")
    }

    fun runInfoPipeline(input: File, prefix: String) {
        val (pous, errors) = IEC61131Facade.fileResolve(input)
        errors.forEach {
            info("${it.sourceName}:${it.startLine} :: ${it.message} (${it.category}) ")
        }

        val program = Utils.findProgram(pous)!!

        //Custom program transformation
        AssignmentDScratch.transform(
                SeqParamsActiveStep.transform(TransformationState(program))
        )

        val simplified = SymbExFacade.simplify(program)

        UsageFinder.markVariablesByUsage(simplified)

        //Custom program transformation
        val t = MultiCodeTransformation(
                RealToInt(),
                RemoveVSObj,
                RemoveConversionFunction,
                IntLit1000To1
        )
        t.transform(TransformationState(simplified))

        markVariableAs(simplified.scope,
                "stHmiInt\$rStartVel",
                "stHmiInt\$stMCStatus\$bMC_Error",
                "stHmiInt\$stReq\$stMan\$bDecrVel",
                "stHmiInt\$stReq\$stMan\$bDisable",
                "stHmiInt\$stReq\$stMan\$bIncrVel",
                "stHmiInt\$stReq\$stMan\$bStartVel",
                flag = VariableDeclaration.INPUT)

        val simpFile = File(FOLDER, "Simplified.st")
        simpFile.bufferedWriter().use {
            IEC61131Facade.printTo(it, simplified, true)
        }
        info("File $simpFile written")

        val module = SymbExFacade.evaluateProgram(simplified, true)
        val isHigh = { v: String ->
            val b = v in listOf(
                    //unused: "ReadStatusAxis1\$ConstantVelocity"
                    //ReadActVelAxis1.Velocity
                    "ActStep\$rVelocity"
                    //,"MoveVelAxis1\$InVelocity"
                    //,"ReadActVelAxis1\$Velocity"
            )// v.endsWith("Velocity")
            info(String.format("%35s %s", v, (if (b) "high" else "low")))
            b
        }

        for (historyLength in listOf(2, 3, 5, 7, 10)) {
            //val imb = IFModelBuilder(module, isHigh)
            val imb = PrivacyModelBuilder(module, isHigh, historyLength)
            imb.run()

            val smvFile = File(FOLDER, String.format(prefix, imb.historyLength))
            smvFile.bufferedWriter().use {
                imb.product.forEach { m -> m.accept(SMVPrinter(CodeWriter(it))) }
            }
            info("File $smvFile written")
        }
    }
}



object AssignmentDScratch : STCodeTransformation, AstMutableVisitor() {
    override fun transform(stBody: StatementList): StatementList = stBody.accept(this) as StatementList
    override fun visit(assignmentStatement: AssignmentStatement): Statement {
        if ((assignmentStatement.location as SymbolicReference).identifier == "dScratch") {
            return StatementList()
        }
        return assignmentStatement
    }
}


/**
 * * Self composition
 * * start from two equal states
 * * inserting information
 * * forgetting information in [historyLength] cycles.
 */
class PrivacyModelBuilder(private val code: SMVModule,
                          val isHigh: (String) -> Boolean,
                          val historyLength: Int = 10) : Runnable {
    val strongEqualInVar = SVariable("strongEqualIn", SMVTypes.BOOLEAN)
    val softEqualInVar = SVariable("softEqualIn", SMVTypes.BOOLEAN)
    val hmb = HistoryModuleBuilder("HisStrongEqual",
            listOf(strongEqualInVar),
            historyLength)

    val main = SMVModule("main")
    val product = arrayListOf(main, code, hmb.module)

    override fun run() {
        main.name = MAIN_MODULE

        code.inputVars.addAll(code.moduleParameters)
        code.moduleParameters.clear()

        // forget starting state
        code.initExpr.clear()
        code.initAssignments.clear()

        instantiateCode(FIRST_RUN)
        instantiateCode(SECOND_RUN)

        //info("State: ${code.stateVars.map { it.name }}")

        //equal starting state
        main.initExpr.add(
                code.stateVars
                        .map { it.inModule(FIRST_RUN) equal it.inModule(SECOND_RUN) }
                        .conjunction())

        // low variables
        val lowVar = code.inputVars.filter { !isHigh(it.name) }

        // high variables
        val highVar = code.inputVars.filter { isHigh(it.name) }

        //info("lowVar: ${lowVar.map { it.name }}")
        //info("highVar: ${highVar.map { it.name }}")


        fun conjunction(v: List<SVariable>): SMVExpr {
            if (v.isEmpty()) return SLiteral.TRUE

            val equalities = v.map { it.inModule(FIRST_RUN) equal it.inModule(SECOND_RUN) }
            return equalities.conjunction()
        }

        val lowEqual = conjunction(lowVar)
        val highEqual = conjunction(highVar)

        //first phase, insert information
        val inputLow = lowEqual
        main.definitions.add(softEqualInVar assignTo inputLow)

        // equal output
        val inputEqual = softEqualInVar and highEqual
        main.definitions.add(strongEqualInVar assignTo inputEqual)

        // flag: signals that soft equivalence is maintained
        val alwaysLowEqual = SVariable("__alwaysLowEqual", SMVTypes.BOOLEAN)
        main.stateVars.add(alwaysLowEqual)
        main.initAssignments.add(alwaysLowEqual assignTo SLiteral.TRUE)
        main.nextAssignments.add(alwaysLowEqual assignTo (alwaysLowEqual and softEqualInVar))

        // History of Equal Inputs.
        hmb.run()
        val historyLowEq = SVariable("hInputStrongEq", hmb.moduleType)
        main.stateVars.add(historyLowEq)


        //TODO too many output variables.
        val lowOutput = /*code.definitions.map { it.target } +*/ code.stateVars
        val history = hmb.module.stateVars.map { it.inModule(historyLowEq.name) }
        val premise = (history + strongEqualInVar + alwaysLowEqual)
                .reduce { acc: SMVExpr, sVariable: SMVExpr ->
                    acc.and(sVariable)
                }

        main.invariantSpecs.add(premise implies
                conjunction(lowOutput))

        //    val eq = it.inModule(FIRST_RUN) equal it.inModule(SECOND_RUN)
        //main.invariantSpecs.add( softEqualInVar implies  softEqualInVar)
    }

    private fun instantiateCode(nameOfRun: String) {
        main.stateVars.add(SVariable(nameOfRun, ModuleType(code.name)))
    }

    companion object {
        val SECOND_RUN = "snd"
        val FIRST_RUN = "fst"
        val MAIN_MODULE = "main"
    }
}


class IFModelBuilder(private val code: SMVModule,
                     val isHigh: (String) -> Boolean, private val historyLength: Int = 10) : Runnable {
    val loweq = SVariable("lowEq", SMVTypes.BOOLEAN)
    val hmb = HistoryModuleBuilder("HistoryLowEq", listOf(loweq), historyLength)
    val main = SMVModule("main")
    val product = arrayListOf(main, code, hmb.module)

    override fun run() {
        main.name = MAIN_MODULE

        code.inputVars.addAll(code.moduleParameters)
        code.moduleParameters.clear()

        instantiateCode(FIRST_RUN)
        instantiateCode(SECOND_RUN)

        val inV = code.inputVars
        val inputLow = inV.filter { !isHigh(it.name) }
                .map {
                    it.inModule(FIRST_RUN) equal it.inModule(SECOND_RUN)
                }
                .reduce { a, b -> a and b }

        // History of low inputs.
        hmb.run()
        val historyLowEq = SVariable("hLowEq", hmb.moduleType)
        main.definitions.add(loweq assignTo inputLow)
        main.stateVars.add(historyLowEq)


        val outV = code.definitions.map { it.target } + code.stateVars
        val lowOutput = outV.filter { !isHigh(it.name) }
        /*val softEqualInVar =          outV.filter { !isHigh(it.name) }
                .map {
                    it.inModule(FIRST_RUN) equal it.inModule(SECOND_RUN)
                }
                .reduce { a, b -> a and b }
        */

        val history = hmb.module.stateVars.map { it.inModule(historyLowEq.name) }
        val premise = (history + loweq).reduce { acc: SMVExpr, sVariable: SMVExpr ->
            acc.and(sVariable)
        }

        lowOutput.forEach {
            val eq = it.inModule(FIRST_RUN) equal it.inModule(SECOND_RUN)
            main.invariantSpecs.add(premise implies eq)
        }
        //main.invariantSpecs.add( softEqualInVar implies  softEqualInVar)
    }

    private fun instantiateCode(nameOfRun: String) {
        main.stateVars.add(SVariable(nameOfRun, ModuleType(code.name)))
    }

    companion object {
        val SECOND_RUN = "snd"
        val FIRST_RUN = "fst"
        val MAIN_MODULE = "main"
    }
}


/**
 * Find and tag the variables with the given [flag]
 */
fun markVariableAs(scope: Scope, vararg vars: String, flag: Int) {
    for (variable in scope.variables) {
        if (variable.name in vars)
            variable.type = flag
    }
}


/**
 * Handles access to `aSeqParams[Sequence.iActStep]`
 */
object SeqParamsActiveStep : CodeTransformation, AstMutableVisitor() {
    override fun transform(state: TransformationState): TransformationState {
        val dt = state.scope.resolveDataType("stSeqParams")

        val vd = VariableDeclaration("ActStep",
                0,
                SimpleTypeDeclaration(dt = dt, init = null))
        vd.dataType = dt
        state.scope.variables += vd
        state.stBody = state.stBody.accept(this) as StatementList
        return state
    }

    override fun visit(symbolicReference: SymbolicReference): Expression {
        if (symbolicReference.identifier == "aSeqParams" && symbolicReference.isArrayAccess) {
            try {
                val sub = symbolicReference.subscripts!![0] as SymbolicReference
                if (sub.identifier == "Sequence" && sub.sub?.identifier == "iActStep") {
                    return SymbolicReference("ActStep", symbolicReference.sub)
                }
            } catch (e: ClassCastException) {

            }
        }
        return super.visit(symbolicReference)
    }
}

/**
 * The remaining program contains division, that are not meaningful
 * anymore (because of the degrading of floats to int), i.e.
 * (i/1000)*1000.
 */
object IntLit1000To1 : STCodeTransformation, AstMutableVisitor() {
    val _1000 = BigInteger.valueOf(1000)
    override fun transform(stBody: StatementList): StatementList = stBody.accept(this) as StatementList
    override fun visit(literal: Literal): Expression =
            if (literal is IntegerLit && literal.value == _1000)
                IntegerLit(INT, BigInteger.ONE)
            else
                literal
}

object RemoveConversionFunction : STCodeTransformation, AstMutableVisitor() {
    override fun transform(stBody: StatementList): StatementList = stBody.accept(this) as StatementList

    val regex = ".*_TO_.*".toRegex()
    override fun visit(invocation: Invocation): Expression {
        if (regex.matchEntire(invocation.callee.identifier) != null) {
            return invocation.parameters[0].expression
        }
        return invocation
    }
}

object RemoveVSObj : STCodeTransformation, AstMutableVisitor() {
    override fun transform(stBody: StatementList) = stBody.accept(this) as StatementList

    override fun visit(assignmentStatement: AssignmentStatement): Statement {
        val ident = (assignmentStatement.location as SymbolicReference).identifier
        return if (ident == "VSObj_McFaultDescription")
            return StatementList()
        else assignmentStatement
    }
}