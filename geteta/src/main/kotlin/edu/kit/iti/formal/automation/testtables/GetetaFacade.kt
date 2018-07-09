/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables


import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.EnumerationTypeDeclaration
import edu.kit.iti.formal.automation.st.ast.PouElements
import edu.kit.iti.formal.automation.testtables.algorithms.BinaryModelGluer
import edu.kit.iti.formal.automation.testtables.algorithms.DelayModuleBuilder
import edu.kit.iti.formal.automation.testtables.io.TableReader
import edu.kit.iti.formal.automation.testtables.io.xmv.NuXMVAdapter
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.SReference
import edu.kit.iti.formal.automation.testtables.model.VerificationTechnique
import edu.kit.iti.formal.automation.testtables.model.options.TableOptions
import edu.kit.iti.formal.automation.visitors.Utils
import edu.kit.iti.formal.smv.EnumType
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SVariable
import org.antlr.v4.runtime.CharStreams
import java.io.File
import java.io.IOException
import java.util.*
import javax.xml.bind.JAXBException

object GetetaFacade {
    @JvmStatic
    @Throws(JAXBException::class)
    fun readTable(filename: String): GeneralizedTestTable {
        val tr = TableReader(File(filename))
        tr.run()
        return tr.product
    }

    @Throws(IOException::class)
    fun readProgram(optionValue: String): PouElements {
        val a = IEC61131Facade.file(CharStreams.fromFileName(optionValue))
        IEC61131Facade.resolveDataTypes(a)
        return a
    }

    fun delay(ref: SReference): DelayModuleBuilder {
        return DelayModuleBuilder(ref.variable,
                ref.cycles)
    }


    fun glue(modTable: SMVModule, modCode: SMVModule, options: TableOptions): SMVModule {
        val mg = BinaryModelGluer(options, modTable, modCode)
        mg.run()
        return mg.product
    }

    fun runNuXMV(tableFilename: String,
                 technique: VerificationTechnique, vararg modules: SMVModule): Boolean {
        return runNuXMV(tableFilename, Arrays.asList(*modules), technique)
    }

    fun getHistoryName(variable: SVariable, cycles: Int): String {
        return getHistoryName(variable) + "._$" + cycles
    }

    fun getHistoryName(variable: SVariable): String {
        return variable.name + "__history"
    }

    fun runNuXMV(tableFilename: String,
                 modules: List<SMVModule>, vt: VerificationTechnique): Boolean {
        val adapter = NuXMVAdapter(File(tableFilename), modules)
        adapter.technique = vt
        adapter.run()
        return adapter.isVerified
    }

    fun createSuperEnum(scope: Scope) : EnumType {
        val allowedValues =
                scope.dataTypes.values()
                        .filter { it is EnumerationTypeDeclaration }
                        .map { it as EnumerationTypeDeclaration }
                        .flatMap { it.allowedValues.map { it.text } }
        return EnumType(allowedValues)
    }

    fun createSuperEnum(code: PouElements): SMVType {
        val scope = Utils.findProgram(code)?.scope
        if(scope !=null)
            return createSuperEnum(code)
        throw IllegalStateException("No program found in given source code")
    }
/*
    private class SuperEnumCreator : AstVisitor<Unit?>() {
        override fun defaultVisit(obj: Any): Unit? = null
        private val seq = ArrayList<String>()
        private val type = EnumType(seq)

        fun getType(): SMVType {
            return type
        }

        override fun visit(etd: EnumerationTypeDeclaration): Unit? {
            seq.addAll(etd.allowedValues.map { it.text })
            return null
        }
    }*/
}
