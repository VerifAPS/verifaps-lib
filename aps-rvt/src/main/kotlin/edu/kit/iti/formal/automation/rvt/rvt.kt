package edu.kit.iti.formal.automation.rvt

import edu.kit.iti.formal.automation.smv.ModuleBuilder
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (12.06.17)
 */
open class RegressionVerification(
        var newVersion: SMVModule,
        var oldVersion: SMVModule,
        var debug: Boolean = false) {

    val glueModule = SMVModuleImpl()

    val oldModuleType = SMVType.Module(oldVersion.name)
    val newModuleType = SMVType.Module(newVersion.name)

    protected fun commonInputVariables(): Set<Pair<SVariable, SVariable>> {
        val set = HashSet<Pair<SVariable, SVariable>>()
        for (oldVar in oldVersion.moduleParameter) {
            for (newVar in newVersion.moduleParameter) {
                if (oldVar.name == newVar.name) {
                    set.add(Pair(oldVar, newVar))
                }
            }
        }
        return set
    }

    protected fun commonOutputVariables(): Set<Pair<SVariable, SVariable>> {
        val set = HashSet<Pair<SVariable, SVariable>>()
        val filterOutput = { k: SVariable -> k.hasMetadata(ModuleBuilder.OUTPUT_VARIABLE) }

        val oldStateVars = oldVersion.stateVars.filter(filterOutput)
        val newStateVars = newVersion.stateVars.filter(filterOutput)

        for (oldVar in oldStateVars) {
            for (newVar in newStateVars) {
                if (oldVar.name == newVar.name) {
                    set.add(Pair(oldVar, newVar))
                }
            }
        }
        return set
    }

    private fun staticInitModule() {
        glueModule.name = "main"
    }

    protected fun addInputVariables() {
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
    protected fun handleSpecialInputVariables(uncoveredOld: List<SVariable>, uncoveredNew: List<SVariable>) {

    }

    protected fun addStateVariables() {
        val oldModuleInstance = SVariable.create("__old__").with(oldModuleType)
        val newModuleInstance = SVariable.create("__new__").with(newModuleType)
        glueModule.stateVars.add(oldModuleInstance)
        glueModule.stateVars.add(newModuleInstance)
    }


    protected fun addProofObligation(oldName: String, newName: String) {
        val output = commonOutputVariables()
        val list = ArrayList<SMVExpr>()


        for ((fst, snd) in output) {
            glueModule.definitions.put(
                    fst,
                    fst.inModule(oldName).equal(snd.inModule(newName))
            )
            list.add(fst)
        }

        val equalOutputExpr = SMVFacade.combine(SBinaryOperator.AND, list)

        glueModule.ltlSpec.add(equalOutputExpr.globally())
        glueModule.invarSpec.add(equalOutputExpr)
    }


    public fun run() {
        staticInitModule()
        addInputVariables()
        addStateVariables()
        addProofObligation("__old__", "__new__")//TODO fix constants or SVariables
    }
}
