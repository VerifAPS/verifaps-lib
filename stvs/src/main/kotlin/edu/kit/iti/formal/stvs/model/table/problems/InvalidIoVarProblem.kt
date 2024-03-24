package edu.kit.iti.formal.stvs.model.table.problems

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable
import edu.kit.iti.formal.stvs.model.expressions.*

/**
 *
 * A problem for when a column is not valid. This problem is generated when the column
 * variable has no matching [CodeIoVariable] or has an unknown / undefined type.
 *
 * @author Benjamin Alt
 * @author Philipp
 */
class InvalidIoVarProblem private constructor(val specIoVariable: SpecIoVariable?, private val errorType: ErrorType) :
    ColumnProblem(
        createMessageForType(
            errorType
        ), specIoVariable!!.name
    ) {
    enum class ErrorType {
        NAME_INVALID, TYPE_UNKNOWN,

        NAME_MISMATCH, TYPE_MISMATCH, CATEGORY_MISMATCH
    }

    fun getErrorType(): ErrorType? {
        return errorType
    }

    override fun equals(obj: Any?): Boolean {
        if (this === obj) {
            return true
        }
        if (obj == null || javaClass != obj.javaClass) {
            return false
        }
        if (!super.equals(obj)) {
            return false
        }

        val that = obj as InvalidIoVarProblem

        if (if (specIoVariable != null) specIoVariable != that.specIoVariable
            else that.specIoVariable != null
        ) {
            return false
        }
        return getErrorType() == that.getErrorType()
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + (if (specIoVariable != null) specIoVariable.hashCode() else 0)
        result = 31 * result + (if (getErrorType() != null) getErrorType().hashCode() else 0)
        return result
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
        @Throws(InvalidIoVarProblem::class)
        fun tryGetValidIoVariable(
            specIoVariable: SpecIoVariable?,
            codeIoVariables: Collection<CodeIoVariable>, typesByName: Map<String, Type>,
            minorProblemsHandler: MinorProblemsHandler
        ): ValidIoVariable {
            val name = tryGetValidName(specIoVariable, codeIoVariables, minorProblemsHandler)
            val type = tryGetValidType(specIoVariable, typesByName, codeIoVariables, minorProblemsHandler)

            return ValidIoVariable(specIoVariable!!.category, name!!, type)
        }

        @Throws(InvalidIoVarProblem::class)
        private fun tryGetValidType(
            specIoVariable: SpecIoVariable?, typesByName: Map<String, Type>,
            codeIoVariables: Collection<CodeIoVariable>, minorProblemsHandler: MinorProblemsHandler
        ): Type {
            val type = typesByName[specIoVariable!!.type]
                ?: throw InvalidIoVarProblem(specIoVariable, ErrorType.TYPE_UNKNOWN)
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

        @Throws(InvalidIoVarProblem::class)
        private fun tryGetValidName(
            ioVar: SpecIoVariable?,
            codeIoVariables: Collection<CodeIoVariable>, minorProblemsHandler: MinorProblemsHandler
        ): String? {
            if (!VariableExpr.Companion.IDENTIFIER_PATTERN.matcher(ioVar!!.name).matches()) {
                throw InvalidIoVarProblem(ioVar, ErrorType.NAME_INVALID)
            }
            if (!codeIoVariables.stream()
                    .anyMatch { codeIoVar: CodeIoVariable -> codeIoVar.name == ioVar.name }
            ) {
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
