package edu.kit.iti.formal.automation.st0

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.st0.trans.*
import edu.kit.iti.formal.automation.st.ast.*

import java.util.ArrayList
import java.util.HashMap

/**
 * @author Alexander Weigl (26.06.2014), Augusto Modanese
 * @version 1
 */
class STSimplifier(inputElements: PouElements) {
    internal val transformations = ArrayList<ST0Transformation>()
    private val state = State()

    val processed: PouElements
        get() {
            val l = PouElements()
            l.add(state.allTypeDeclaration)
            l.addAll(state.functions.values)
            l.add(state.theProgram!!)
            return l
        }

    init {
        state.inputElements = inputElements
    }

    fun addDefaultPipeline() {
        transformations.add(GlobalVariableListEmbedding())
        transformations.add(FunctionBlockEmbedding())
        transformations.add(LoopUnwinding.transformation)
        transformations.add(TimerToCounter.INSTANCE)
        transformations.add(ArrayEmbedder())
        transformations.add(StructEmbedding())
        //transformations.add(SFCResetReplacer.getINSTANCE());
        transformations.add(RemoveActionsFromProgram())
        transformations.add(ConstantEmbedder())  // EXPERIMENTAL
        //transformations.add(TrivialBranchReducer())  // EXPERIMENTAL
    }

    fun transform() {
        initializeState()
        for (t in transformations) {
            t.transform(state)
        }
    }

    fun getTransformations(): List<ST0Transformation> {
        return transformations
    }

    /**
     * Register FUNCTION AND FUNCTIONBLOCKS
     */
    fun initializeState() {
        var programs = 0
        for (tle in state.inputElements!!) {
            if (tle is ProgramDeclaration) {
                programs++
                state.theProgram = tle
            } else if (tle is FunctionBlockDeclaration) {
                state.functionBlocks[tle.name] = tle
            } else if (tle is TypeDeclarations) {
                appendTypeDeclarations(tle)
            } else if (tle is FunctionDeclaration) {
                state.functions[tle.name] = tle
            } else if (tle is GlobalVariableListDeclaration) {
                val (scope) = tle
                state.globalVariableList.scope.addVariables(scope)
            } else {
                throw IllegalArgumentException("TLE: " + tle.javaClass + " isType not handled yet.")
            }
        }

        if (programs != 1 || state.theProgram == null) {
            println(state.inputElements!!.size)
            throw IllegalArgumentException("There must be exactly one program in the List of TLE. " + programs + " found. Elements: " + state.inputElements!!.size)
        }
    }

    /**
     * @return Whether we are transforming OO code
     */
    /*public boolean isTransformingOO() {
        return state.stooState != null;
    }*/

    private fun appendTypeDeclarations(typeDeclarations: TypeDeclarations) {
        for (td in typeDeclarations) {
            var allowed = true
            if (td is StructureTypeDeclaration) {
                state.structs[td.name] = td
                continue
            }
            when (td.baseType.identifier) {
                "SINT", "INT", "LINT", "DINT", "UINT", "USINT", "ULINT", "UDINT", "BOOL", "ENUM" -> allowed = true
                else -> allowed = false
            }
            if (allowed)
                state.allTypeDeclaration.add(td)
            else
                throw IllegalArgumentException("There isType an unsupported type declared! " + td.name + " with baseType type " + td.baseType)
        }
    }

    class State {
        var inputElements: PouElements? = null
        var theProgram: ProgramDeclaration? = null
        var functionBlocks: MutableMap<String, FunctionBlockDeclaration> = HashMap()
        var functions: MutableMap<String, FunctionDeclaration> = HashMap()
        var structs: MutableMap<String, StructureTypeDeclaration> = HashMap()
        var allTypeDeclaration = TypeDeclarations()
        var globalVariableList: GlobalVariableListDeclaration = GlobalVariableListDeclaration()
        //public STOOSimplifier.State stooState;
    }

    companion object {
        val PROGRAM_VARIABLE = VariableDeclaration.FLAG_COUNTER.get()
    }
}
