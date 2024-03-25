package edu.kit.iti.formal.stvs

import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator
import edu.kit.iti.formal.stvs.model.common.FreeVariableProblem
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable
import edu.kit.iti.formal.stvs.model.config.GlobalConfig.Companion.autoloadConfig
import edu.kit.iti.formal.stvs.model.expressions.*
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.table.ValidSpecification
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator
import javafx.beans.property.SimpleListProperty
import javafx.collections.FXCollections
import javafx.stage.FileChooser
import org.junit.Assume
import org.mockito.ArgumentMatchers
import org.mockito.Mockito
import org.powermock.api.mockito.PowerMockito
import org.testfx.util.WaitForAsyncUtils
import tornadofx.asObservable
import java.io.*
import java.net.URL
import java.util.*
import java.util.concurrent.TimeUnit
import java.util.stream.Collectors

/**
 * Created by bal on 10.02.17.
 */
object TestUtils {
    /**
     * Tolerance for floating-point rounding errors when doing assertEquals() with doubles
     */
    const val EPSILON: Double = 0.001

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
            val validSpec = validator.getValidSpecification()
            if (validSpec == null) {
                System.err.println("ConstraintSpecification could not be validated:")
                validator.problemsProperty().get().map { it?.errorMessage }.forEach { System.err.println(it) }
                throw RuntimeException("Couldn't validate Specification")
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
        val validator = FreeVariableListValidator(SimpleListProperty(typeContext.asObservable()), freeVariableList!!)
        if (validator.problemsProperty.get().isNotEmpty()) {
            System.err.println("Could not validate free variables:")
            validator.problemsProperty.get().map { (k, v) ->
                "$k -> " + v.map(FreeVariableProblem::guiMessage)
            }.forEach(System.err::println)
            throw RuntimeException("Couldn't validate")
        }
        return validator.validFreeVariablesProperty.get()
    }

    fun gimmeTime() {
        WaitForAsyncUtils.sleep(5, TimeUnit.SECONDS)
    }

    @Throws(Exception::class)
    fun mockFiles(vararg urls: URL) {
        val files = Arrays.stream(urls)
            .map { obj: URL -> obj.path }
            .map { pathname: String? -> File(pathname) }
            .collect(Collectors.toList())
        val chooser = Mockito.mock(FileChooser::class.java)
        var stub = Mockito.`when`(chooser.showOpenDialog(ArgumentMatchers.any()))
        for (file in files) {
            stub = stub.thenReturn(file)
        }
        Mockito.`when`(chooser.extensionFilters).thenReturn(FXCollections.observableList(ArrayList()))
        PowerMockito.whenNew(FileChooser::class.java).withAnyArguments().thenReturn(chooser)
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