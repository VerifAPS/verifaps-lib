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
package edu.kit.iti.formal.stvs

import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.code.Code
import edu.kit.iti.formal.stvs.model.code.CodeTest
import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator
import edu.kit.iti.formal.stvs.model.common.FreeVariableProblem
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable
import edu.kit.iti.formal.stvs.model.config.GlobalConfig.Companion.autoloadConfig
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.table.ValidSpecification
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator
import javafx.beans.property.SimpleListProperty
import javafx.collections.FXCollections
import org.junit.Assume
import tornadofx.asObservable
import java.io.File
import java.io.InputStream
import java.io.InputStreamReader

/**
 * Created by bal on 10.02.17.
 */
object TestUtils {
    /**
     * Tolerance for floating-point rounding errors when doing assertEquals() with doubles
     */
    const val EPSILON: Double = 0.001

    fun loadCodeFromFile(filename: String): Code =
        InputStreamReader(CodeTest::class.java.getResourceAsStream(filename)!!).use {
            Code(filename, it.readText())
        }

    fun loadFromTestSets(resource: String): InputStream =
        TestUtils::class.java.getResourceAsStream("testSets/$resource")!!

    fun importValidSpec(source: InputStream, vararg enumTypes: TypeEnum): ValidSpecification {
        val typeContext: MutableList<Type> = ArrayList()
        typeContext.add(TypeInt)
        typeContext.add(TypeBool)
        for (enumType in enumTypes) {
            typeContext.add(enumType)
        }
        return importValidSpec(source, typeContext)
    }

    fun importValidSpec(source: InputStream, typeContext: List<Type>): ValidSpecification {
        try {
            val constraintSpec: ConstraintSpecification =
                ImporterFacade.importConstraintSpec(source)
            val validFreeVariables = importValidFreeVariables(
                constraintSpec.freeVariableList,
                typeContext,
            )
            val validator = ConstraintSpecificationValidator(
                SimpleListProperty(typeContext.asObservable()),
                SimpleListProperty(FXCollections.observableArrayList()),
                validFreeVariables.asObservable(),
                constraintSpec,
            )
            val validSpec = validator.validSpecification
            if (validSpec == null) {
                System.err.println("ConstraintSpecification could not be validated:")
                validator.problemsProperty.get().map { it?.errorMessage }.forEach { System.err.println(it) }
                throw RuntimeException("Couldn't validate specification")
            }
            return validSpec
        } catch (cause: ImportException) {
            throw RuntimeException(cause)
        }
    }

    fun importValidFreeVariables(source: InputStream, vararg enumTypes: TypeEnum): List<ValidFreeVariable> {
        val typeContext: MutableList<Type> = ArrayList()
        typeContext.add(TypeInt)
        typeContext.add(TypeBool)
        for (enumType in enumTypes) {
            typeContext.add(enumType)
        }
        try {
            return importValidFreeVariables(
                ImporterFacade.importConstraintSpec(source).freeVariableList,
                typeContext,
            )
        } catch (ex: ImportException) {
            throw RuntimeException(ex)
        }
    }

    fun importValidFreeVariables(freeVariableList: FreeVariableList, typeContext: List<Type>): List<ValidFreeVariable> {
        val validator = FreeVariableListValidator(SimpleListProperty(typeContext.asObservable()), freeVariableList)
        if (validator.problemsProperty.get().isNotEmpty()) {
            System.err.println("Could not validate free variables:")
            validator.problemsProperty.get().map { (k, v) ->
                "$k -> " + v.map(FreeVariableProblem::guiMessage)
            }.forEach(System.err::println)
            throw RuntimeException("Couldn't validate")
        }
        return validator.validFreeVariablesProperty.get()
    }

    private fun assumeFileExists(message: String, executable: String) {
        Assume.assumeTrue(message, File(executable).exists())
    }

    fun assumeZ3Exists() {
        assumeFileExists(
            "The z3 command is not set or a non-existing file. Tests are skipped!",
            autoloadConfig().z3Path,
        )
    }

    fun assumeNuXmvExists() {
        assumeFileExists(
            "The nuxmv command is not set or a non-existing file. Tests are skipped!",
            autoloadConfig().nuxmvFilename,
        )
    }
}