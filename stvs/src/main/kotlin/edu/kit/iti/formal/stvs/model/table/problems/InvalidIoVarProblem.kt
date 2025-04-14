package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.Selection
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.VariableExpr

/**
 *
 * A problem for when a column is not valid. This problem is generated when the column
 * variable has no matching [CodeIoVariable] or has an unknown / undefined type.
 *
 * @author Benjamin Alt
 * @author Philipp
 */
data class InvalidIoVarProblem(
    val specIoVariable: SpecIoVariable, private val errorType: ErrorType
) : ColumnProblem {
    override val column: String
        get() = specIoVariable.name
    override val errorMessage: String
        get() = createMessageForType(errorType)

    override val location: Selection = Selection(specIoVariable.name)

    enum class ErrorType {
        NAME_INVALID, TYPE_UNKNOWN,
        NAME_MISMATCH, TYPE_MISMATCH,
        CATEGORY_MISMATCH
    }

    companion object {
        /**
         * Tries to get a formal model ([ValidIoVariable]) from the given effective model
         * ([SpecIoVariable]).
         *
         * @param specIoVariable the effective model of column headers
         * @param codeIoVariables the io variables that were extracted form the code
         * @param typesByName the types that were extracted from the code
         * @param minorProblemsHandler the handler that is invoked, when a minor problem is generated,
         * that is, a problem that does not prevent this method from creating
         * an instance of [ValidIoVariable], for example a mismatch
         * between the given variable and a code io variable
         * @return the formal model for column headers
         * @throws InvalidIoVarProblem if there was a fatal error while creating a formal model
         * for column headers (for example the type is not defined in code)
         */
        @Throws(SpecProblemException::class)
        fun tryGetValidIoVariable(
            specIoVariable: SpecIoVariable,
            codeIoVariables: Collection<CodeIoVariable>, typesByName: Map<String, Type>,
            minorProblemsHandler: MinorProblemsHandler
        ): ValidIoVariable {
            val name = tryGetValidName(specIoVariable, codeIoVariables, minorProblemsHandler)
            val type = tryGetValidType(specIoVariable, typesByName, codeIoVariables, minorProblemsHandler)
            val role = specIoVariable.role
            return ValidIoVariable(specIoVariable.category, name, type, role)
        }

        @Throws(SpecProblemException::class)
        private fun tryGetValidType(
            specIoVariable: SpecIoVariable, typesByName: Map<String, Type>,
            codeIoVariables: Collection<CodeIoVariable>, minorProblemsHandler: MinorProblemsHandler
        ): Type {
            val type = typesByName[specIoVariable.type] ?: throw InvalidIoVarProblem(
                specIoVariable,
                ErrorType.TYPE_UNKNOWN
            ).asException()
            codeIoVariables.stream()
                .filter { codeIoVariable: CodeIoVariable -> codeIoVariable.name == specIoVariable.name }
                .findAny().ifPresent { codeIoVariable: CodeIoVariable ->
                    if (codeIoVariable.type != specIoVariable.type) {
                        minorProblemsHandler
                            .handle(InvalidIoVarProblem(specIoVariable, ErrorType.TYPE_MISMATCH))
                    }
                }
            return type
        }

        @Throws(SpecProblemException::class)
        private fun tryGetValidName(
            ioVar: SpecIoVariable,
            codeIoVariables: Collection<CodeIoVariable>,
            minorProblemsHandler: MinorProblemsHandler
        ): String {
            if (!VariableExpr.IDENTIFIER_PATTERN.matcher(ioVar.name).matches()) {
                throw InvalidIoVarProblem(ioVar, ErrorType.NAME_INVALID).asException()
            }
            if (!codeIoVariables.any { it.name == ioVar.name }) {
                minorProblemsHandler.handle(InvalidIoVarProblem(ioVar, ErrorType.NAME_MISMATCH))
            }
            return ioVar.name
        }

        private fun createMessageForType(errorType: ErrorType): String {
            when (errorType) {
                ErrorType.NAME_MISMATCH -> return "Column name in table doesn't match any column name in code"
                ErrorType.TYPE_MISMATCH -> return "Column type in table doesn't match column type in code"
                ErrorType.CATEGORY_MISMATCH -> return "Column category in table doesn't match column category in code"
                ErrorType.NAME_INVALID -> return "Column name is not a valid identifier"
                ErrorType.TYPE_UNKNOWN -> return "Column type is not defined"
                else -> {
                    System.err
                        .println("Unhandled error message errorType in InvalidIoVariableProblem: $errorType")
                    return "Column definition invalid"
                }
            }
        }
    }
}
