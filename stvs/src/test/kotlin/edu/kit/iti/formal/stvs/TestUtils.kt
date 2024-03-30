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

    fun loadCodeFromFile(filename: String): Code {
        return InputStreamReader(CodeTest::class.java.getResourceAsStream(filename)!!).use {
            Code(filename, it.readText())
        }
    }

    fun loadFromTestSets(resource: String): InputStream {
        return TestUtils::class.java.getResourceAsStream("testSets/$resource")!!
    }

    fun importValidSpec(source: InputStream, vararg enumTypes: TypeEnum): ValidSpecification {
        val typeContext: MutableList<Type> = ArrayList()
        typeContext.add(TypeInt.INT)
        typeContext.add(TypeBool.BOOL)
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
                constraintSpec.freeVariableList, typeContext
            )
            val validator = ConstraintSpecificationValidator(
                SimpleListProperty(typeContext.asObservable()),
                SimpleListProperty(FXCollections.observableArrayList()),
                validFreeVariables.asObservable(),
                constraintSpec
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
        typeContext.add(TypeInt.INT)
        typeContext.add(TypeBool.BOOL)
        for (enumType in enumTypes) {
            typeContext.add(enumType)
        }
        try {
            return importValidFreeVariables(
                ImporterFacade.importConstraintSpec(source).freeVariableList,
                typeContext
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
            autoloadConfig().z3Path
        )
    }

    fun assumeNuXmvExists() {
        assumeFileExists(
            "The nuxmv command is not set or a non-existing file. Tests are skipped!",
            autoloadConfig().nuxmvFilename
        )
    }

    fun assumeGetetaExists() {
        val toks = autoloadConfig().getetaCommand
            .split(" ".toRegex()).dropLastWhile { it.isEmpty() }.toTypedArray()
        assumeFileExists(
            "The geteta command is not set or a non-existing file. Tests are skipped!",
            toks[0]
        )
    }
}