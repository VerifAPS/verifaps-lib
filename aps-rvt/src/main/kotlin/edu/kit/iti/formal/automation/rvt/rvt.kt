package edu.kit.iti.formal.automation.rvt

import edu.kit.iti.formal.automation.smv.ModuleBuilder
import edu.kit.iti.formal.smv.Printer
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.*
import mu.KLogging
import java.io.Writer

/**
 *
 */
fun commonVariables(a: Collection<out SVariable>,
                    b: Collection<out SVariable>,
                    pred: SVarEquals)
        : Set<Pair<SVariable, SVariable>> {
    val set = HashSet<Pair<SVariable, SVariable>>()
    for (oldVar in a) {
        for (newVar in b) {
            if (pred(oldVar, newVar)) {
                set.add(Pair(oldVar, newVar))
            }
        }
    }
    return set
}


/**
 *
 */
typealias SVarEquals = (SVariable, SVariable) -> Boolean


val nameEqual: SVarEquals = { a, b -> a.name == b.name }


/**
 *
 * @author Alexander Weigl
 * @version 1 (12.06.17)
 */
open class RegressionVerification(
        var newVersion: SMVModule,
        var oldVersion: SMVModule) {

    val glueModule = SMVModule()

    var oldModuleType: SMVType.Module? = null
    var newModuleType: SMVType.Module? = null

    val oldInstanceName = "__old__"
    val newInstanceName = "__new__"

    companion object : KLogging()

    protected open fun commonInputVariables(): Set<Pair<SVariable, SVariable>> {
        return commonVariables(oldVersion.moduleParameter, newVersion.moduleParameter, nameEqual)
    }

    protected open fun commonOutputVariables(): Set<Pair<SVariable, SVariable>> {
        return edu.kit.iti.formal.automation.rvt.commonOutputVariables(oldVersion, newVersion, nameEqual)
    }

    protected open fun staticInitModule() {
        glueModule.name = "main"

        if (newVersion.name == oldVersion.name) {
            newVersion.name += "_new"
            oldVersion.name += "_old"
            logger.info("modules renamed due to collision")
        }
        newModuleType = SMVType.Module(newVersion.name)
        oldModuleType = SMVType.Module(oldVersion.name)
    }

    protected open fun addInputVariables() {
        val commonInput = commonInputVariables()
        val uncoveredOld = ArrayList<SVariable>(oldVersion.moduleParameter)
        val uncoveredNew = ArrayList<SVariable>(newVersion.moduleParameter)

        for ((first, second) in commonInput) {
            assert(first.datatype == second.datatype) { "Datatypes are not equal for ${first} and ${second}" }
            glueModule.inputVars.add(first)

            uncoveredOld.remove(first)
            uncoveredNew.remove(second)
        }

        handleSpecialInputVariables(uncoveredOld, uncoveredNew);
    }

    /**
     * @param uncoveredOld
     * @param uncoveredNew
     */
    protected open fun handleSpecialInputVariables(uncoveredOld: List<SVariable>, uncoveredNew: List<SVariable>) {

    }

    protected open fun addStateVariables() {
        val oldModuleInstance = SVariable.create("__old__").with(oldModuleType)
        val newModuleInstance = SVariable.create("__new__").with(newModuleType)
        glueModule.stateVars.add(oldModuleInstance)
        glueModule.stateVars.add(newModuleInstance)
    }


    protected open fun addProofObligation(oldName: String, newName: String) {
        val output = commonOutputVariables()
        val list = ArrayList<SMVExpr>()


        for ((fst, snd) in output) {
            val eq = SVariable.bool("eq_${fst.name}_${snd.name}")
            glueModule.definitions.put(
                    eq,
                    fst.inModule(oldName).equal(snd.inModule(newName))
            )
            list.add(eq)
        }

        val equalOutputExpr = if (list.isEmpty()) SLiteral.TRUE
        else SMVFacade.combine(SBinaryOperator.AND, list)

        glueModule.ltlSpec.add(equalOutputExpr.globally())
        glueModule.invarSpec.add(equalOutputExpr)
    }


    public fun run() {
        staticInitModule()
        addInputVariables()
        addStateVariables()
        addProofObligation(oldInstanceName, newInstanceName)
        //TODO fix constants or SVariables

    }

    open fun writeTo(writer: Writer) {
        with(writer) {
            this.write(edu.kit.iti.formal.smv.Printer.toString(glueModule))
            val sep = "-".repeat(80) + "\n"
            this.write(sep)
            this.write(edu.kit.iti.formal.smv.Printer.toString(oldVersion))
            this.write(sep)
            this.write(edu.kit.iti.formal.smv.Printer.toString(newVersion))
            this.write(sep)
        }
    }
}


private fun commonOutputVariables(oldVersion: SMVModule, newVersion: SMVModule, pred: SVarEquals):
        Set<Pair<SVariable, SVariable>> {
    return commonVariables(oldVersion.outputVars, newVersion.outputVars, pred)
}

val filterOutput = { k: SVariable -> k.hasMetadata(ModuleBuilder.OUTPUT_VARIABLE) }
private val SMVModule.outputVars: Collection<SVariable>
    get() {
        return this.stateVars.filter(filterOutput)
    }

abstract class Miter(val oldVersion: SMVModule, val newVersion: SMVModule) {
    var module = SMVModule()
    val parameterIsNew: MutableList<Pair<SVariable, Boolean>> = arrayListOf()
    var varSystemEq: SVariable? = null
    val oldPrefix = "o_"
    val newPrefix = "n_"
    var ltlSpec: SQuantified? = null
    var invarSpec: SMVExpr? = null
    abstract fun build()
    open fun writeTo(writer: Writer) {
        writer.write(Printer.toString(module))
    }
}

open class ReVeWithMiter(oldVersion: SMVModule, newVersion: SMVModule, val miter: Miter)
    : RegressionVerification(newVersion, oldVersion) {
    var miterInstanceName = "__miter__"

    override fun addProofObligation(oldName: String, newName: String) {
        miter.build()
        val parameters =
                miter.parameterIsNew
                        .map {
                            it.first.inModule(if (it.second) newName
                            else oldName)
                        }

        val miterVar = SVariable.create(miterInstanceName).with(
                SMVType.Module(miter.module.name, parameters)
        )

        glueModule.stateVars.add(miterVar)
        glueModule.ltlSpec.add(miter.ltlSpec?.inModule(miterInstanceName))
        glueModule.invarSpec.add(miter.invarSpec?.inModule(miterInstanceName))
    }

    override fun writeTo(writer: Writer) {
        super.writeTo(writer)
        miter.writeTo(writer)
    }
}

open class GloballyMiter(oldVersion: SMVModule, newVersion: SMVModule)
    : Miter(oldVersion, newVersion) {


    override fun build() {
        module.name = "GloballyMiter"
        val output = commonOutputVariables(oldVersion, newVersion, nameEqual)
        val list = ArrayList<SMVExpr>()

        for (v in oldVersion.moduleParameter + oldVersion.stateVars) {
            module.moduleParameter.add(v.prefix(oldPrefix))
            parameterIsNew += Pair(v, false)
        }

        for (v in newVersion.moduleParameter + newVersion.stateVars) {
            module.moduleParameter.add(v.prefix(newPrefix))
            parameterIsNew += Pair(v, true)
        }


        for ((fst, snd) in output) {
            val eq = SVariable.bool("eq_${fst.name}_${snd.name}")
            val old = fst.prefix(oldPrefix)
            val new = snd.prefix(newPrefix)
            module.definitions.put(eq, old.equal(new))
            list.add(eq)
        }

        val equalOutputExpr = if (list.isEmpty()) SLiteral.TRUE
        else SMVFacade.combine(SBinaryOperator.AND, list)

        ltlSpec = equalOutputExpr.globally()
        invarSpec = equalOutputExpr
    }
}

private fun SVariable.prefix(prefix: String): SVariable {
    return SVariable(prefix + this.name, this.datatype)
}

open class UntilMiter(oldVersion: SMVModule, newVersion: SMVModule, val inner: Miter)
    : Miter(oldVersion, newVersion) {
    var triggerCondition = SVariable.bool("END_TRIGGER_POINT")

    open fun event(expr: SMVExpr) {
        module.definitions[triggerCondition] = expr
    }

    override fun build() {
        inner.build()
        module.name = "UntilMiter"
        module.moduleParameter.addAll(inner.module.moduleParameter)

        module.stateVars.add(
                SVariable.create("inner")
                        .with(SMVType.Module(inner.module.name,
                                inner.module.moduleParameter))
        )

        val end = SVariable.bool("premise")
        module.stateVars.add(end)
        module.initAssignments.add(
                SAssignment(end, SLiteral.TRUE))
        module.nextAssignments.add(
                // next(premise) = premise & !EVENT
                SAssignment(end, end.and(triggerCondition.not())))

        invarSpec = end.implies(inner.invarSpec?.inModule("inner"))
    }

    override fun writeTo(writer: Writer) {
        super.writeTo(writer)
        inner.writeTo(writer)
    }
}