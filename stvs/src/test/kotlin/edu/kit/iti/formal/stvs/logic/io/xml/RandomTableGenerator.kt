package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade
import edu.kit.iti.formal.stvs.model.common.FreeVariable
import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import edu.kit.iti.formal.stvs.model.common.VariableCategory
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory.enumOfName
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConstraintCell
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.table.SpecificationRow
import java.io.File
import java.io.IOException
import java.util.*

/**
 * A random generator for syntactically valid [ConstraintSpecification]s.
 * @author Benjamin Alt
 */
class RandomTableGenerator {
    private var random: Random
    private var enumTypes: MutableList<TypeEnum>

    constructor() {
        random = Random()
        enumTypes = ArrayList()
    }

    constructor(seed: Long) {
        random = Random(seed)
        enumTypes = ArrayList()
    }

    /**
     * Create a new random [ConstraintSpecification].
     * @param columns The number of columns in the random specification
     * @param rows The number of rows in the random specification
     * @param freeVariables The number of free variables in the random specification
     * @return The random specification
     */
    fun randomConstraintSpec(columns: Int, rows: Int, freeVariables: Int): ConstraintSpecification {
        val freeVariableList = FreeVariableList()
        for (i in 0 until freeVariables) {
            freeVariableList.variables.add(randomFreeVariable(freeVariableList))
        }
        val constraintSpec = ConstraintSpecification(freeVariableList)
        constraintSpec.name = randomAlphaNumeric(random.nextInt(MAX_NAME_LENGTH))
        constraintSpec.comment = randomAlphaNumeric(random.nextInt(MAX_COMMENT_LENGTH))
        for (i in 0 until columns) {
            constraintSpec.columnHeaders.add(randomSpecIoVariable(constraintSpec.columnHeaders))
        }
        for (i in 0 until rows) {
            constraintSpec.rows.add(
                randomSpecificationRow(
                    constraintSpec.columnHeaders,
                    freeVariableList
                )
            )
            constraintSpec.durations.add(randomDuration())
        }
        return constraintSpec
    }

    private fun randomDuration(): ConstraintDuration {
        val randomInt = random.nextInt(10)
        if (randomInt < 3) {
            return ConstraintDuration("-")
        }
        if (randomInt < 6) {
            val lowerBound = random.nextInt(10)
            return ConstraintDuration("[" + lowerBound.toString() + "," + (lowerBound + random.nextInt(10)).toString() + "]")
        }
        return ConstraintDuration("[" + random.nextInt(10).toString() + ",-]")
    }

    private fun randomSpecificationRow(
        columnHeaders: List<SpecIoVariable>,
        freeVariableList: FreeVariableList
    ): SpecificationRow<ConstraintCell> {
        val cells = hashMapOf<String, ConstraintCell>()
        for (ioVariable in columnHeaders) {
            val cell = randomConstraintCell(ioVariable, columnHeaders, freeVariableList)
            cells[ioVariable.name] = cell
        }
        val row = SpecificationRow(cells, { _ -> arrayOf() })
        if (random.nextBoolean()) {
            row.comment = randomAlphaNumeric(MAX_COMMENT_LENGTH)
        }
        return row
    }

    private fun randomConstraintCell(
        ioVariable: SpecIoVariable,
        columnHeaders: List<SpecIoVariable>,
        freeVariableList: FreeVariableList
    ): ConstraintCell {
        val cellString: String
        val randomInt = random.nextInt(10)
        cellString = if (randomInt < 9) {
            randomAssignment(ioVariable, columnHeaders, freeVariableList)
        } else {
            "-" // Wildcard with probability 10%
        }
        val cell = ConstraintCell(cellString)
        if (random.nextBoolean()) {
            cell.comment = randomAlphaNumeric(random.nextInt(MAX_COMMENT_LENGTH))
        }
        return cell
    }

    private fun randomAssignment(
        ioVariable: SpecIoVariable,
        columnHeaders: List<SpecIoVariable>,
        freeVariableList: FreeVariableList
    ): String {
        return "=" + randomExpressionOfType(ioVariable, columnHeaders, freeVariableList)
    }

    private fun randomExpressionOfType(
        ioVariable: SpecIoVariable, columnHeaders: List<SpecIoVariable>,
        freeVariableList: FreeVariableList
    ): String {
        return when (ioVariable.type) {
            "INT" -> randomIntegerExpression(columnHeaders, freeVariableList)
            "BOOL" -> randomBooleanExpression(columnHeaders, freeVariableList)
            else -> randomEnumExpression(ioVariable)
        }
    }

    private fun randomEnumExpression(
        ioVariable: SpecIoVariable
    ): String {
        // Enums can only be compared --> boolean expression
        // So the only expression of enum value is a single enum literal
        var enumType: TypeEnum? = null
        for (type in enumTypes) {
            if (ioVariable.type == type.typeName) {
                enumType = type
            }
        }
        checkNotNull(enumType) { "Enum type not found!" }
        return enumType.values[random.nextInt(enumType.values.size)].valueString
    }

    private fun randomIntegerExpression(
        columnHeaders: List<SpecIoVariable>,
        freeVariableList: FreeVariableList
    ): String {
        val randomInt = random.nextInt(10)
        if (randomInt == 1) {
            // random unary expression - there is only one, unary minus
            return "-(" + randomIntegerExpression(columnHeaders, freeVariableList) + ")"
        }
        if (randomInt < 4) {
            // random binary expression
            return ("(" + randomIntegerExpression(columnHeaders, freeVariableList) + " " +
                    randomIntegerBinaryOp() + " " + randomIntegerExpression(columnHeaders, freeVariableList)
                    + ")")
        }
        if (randomInt < 6) {
            // back reference or variable
            val intVariables: MutableList<String> = ArrayList()
            for (`var` in columnHeaders) {
                if (`var`.type == "INT") {
                    intVariables.add(`var`.name)
                }
            }
            if (intVariables.size == 0) return random.nextInt(MAX_INT).toString()
            val varName = intVariables[random.nextInt(intVariables.size)]
            val backReference = random.nextInt(10)
            if (random.nextBoolean()) {
                return "$varName[-$backReference]"
            }
            return varName
        }
        if (randomInt < 8) {
            // free variable
            val intVariables: MutableList<String> = ArrayList()
            for (freeVariable in freeVariableList.variables) {
                if (freeVariable.type == "INT") {
                    intVariables.add(freeVariable.name)
                }
            }
            if (intVariables.size == 0) return random.nextInt(MAX_INT).toString()
            return intVariables[random.nextInt(intVariables.size)]
        }
        // Default: Random integer
        return random.nextInt(MAX_INT).toString()
    }

    private fun randomIntegerBinaryOp(): String {
        return INTEGER_BINARY_OPS[random.nextInt(INTEGER_BINARY_OPS.size)]
    }

    private fun randomBooleanExpression(
        columnHeaders: List<SpecIoVariable>,
        freeVariableList: FreeVariableList
    ): String {
        val randomInt = random.nextInt(10)
        if (randomInt == 0) {
            // random unary op
            return "NOT " + randomBooleanExpression(columnHeaders, freeVariableList)
        }
        if (randomInt == 1) {
            // random binary op
            return ("(" + randomBooleanExpression(columnHeaders, freeVariableList) + " " +
                    randomBooleanBinaryOp() + " " + randomBooleanExpression(columnHeaders, freeVariableList)
                    + ")")
        }
        if (randomInt == 2) {
            return ("(" + randomIntegerExpression(columnHeaders, freeVariableList) + " " +
                    randomComparisonOp() + " " + randomIntegerExpression(columnHeaders, freeVariableList)
                    + ")")
        }
        if (randomInt == 3) {
            // back reference or variable
            val boolVariables: MutableList<String> = ArrayList()
            for (`var` in columnHeaders) {
                if (`var`.type == "BOOL") {
                    boolVariables.add(`var`.name)
                }
            }
            if (boolVariables.size == 0) return if (random.nextBoolean()) "TRUE" else "FALSE"
            val varName = boolVariables[random.nextInt(boolVariables.size)]
            val backReference = random.nextInt(10)
            if (random.nextBoolean()) {
                return "$varName[-$backReference]"
            }
            return varName
        }
        if (randomInt == 4) {
            // free variable
            val boolVariables: MutableList<String> = ArrayList()
            for (freeVariable in freeVariableList.variables) {
                if (freeVariable.type == "BOOL") {
                    boolVariables.add(freeVariable.name)
                }
            }
            if (boolVariables.size == 0) return if (random.nextBoolean()) "TRUE" else "FALSE"
            return boolVariables[random.nextInt(boolVariables.size)]
        }
        // Default: Random literal (TRUE/FALSE)
        return if (random.nextBoolean()) "TRUE" else "FALSE"
    }

    private fun randomComparisonOp(): String {
        return COMPARISON_OPS[random.nextInt(COMPARISON_OPS.size)]
    }

    private fun randomBooleanBinaryOp(): String {
        return BOOLEAN_BINARY_OPS[random.nextInt(BOOLEAN_BINARY_OPS.size)]
    }

    private fun randomSpecIoVariable(specIoVariables: List<SpecIoVariable>): SpecIoVariable {
        val specIoVariableNames = arrayListOf<String>()
        for (v in specIoVariables) {
            specIoVariableNames.add(v.name)
        }
        val name = nonConflictingName(specIoVariableNames)
        return SpecIoVariable(category = randomCategory(), typeIdentifier = randomType().typeName, name = name)
    }

    private fun randomCategory(): VariableCategory {
        val randomInt = random.nextInt(2)
        if (randomInt == 0) {
            return VariableCategory.INPUT
        }
        return VariableCategory.OUTPUT
    }

    private fun randomFreeVariable(freeVariableList: FreeVariableList): FreeVariable {
        val freeVariableNames: MutableList<String> = ArrayList()
        for (freeVar in freeVariableList.variables) {
            freeVariableNames.add(freeVar.name)
        }
        val name = nonConflictingName(freeVariableNames)
        val type = randomType()
        val defaultValue = type.generateDefaultValue()
        return FreeVariable(name, type.typeName, defaultValue.valueString)
    }

    private fun randomType(): Type {
        val randomInt = random.nextInt(10)
        if (randomInt < 3) {
            return TypeInt
        }
        if (randomInt < 6) {
            return TypeBool
        }
        return randomEnumType()
    }

    private fun randomEnumType(): Type {
        if (random.nextBoolean() && enumTypes.size > 0) {
            // Use an existing enum type
            return enumTypes[random.nextInt(enumTypes.size)]
        } else {
            // Create a new enum type
            val numberOfLiterals = random.nextInt(MAX_ENUM_LITERALS)
            val enumLiterals = arrayListOf<String>()
            for (i in 0..numberOfLiterals + 1) {
                enumLiterals.add(nonConflictingName(enumLiterals))
            }
            val enumNames: MutableList<String> = ArrayList()
            for (num in enumTypes) {
                enumNames.add(num.typeName)
            }
            val newEnum = enumOfName(
                nonConflictingName(enumNames),
                *enumLiterals.toTypedArray()
            )
            enumTypes.add(newEnum)
            return newEnum
        }
    }

    private fun nonConflictingName(names: List<String>): String {
        var name = randomIdentifier()
        var nameConflicts = true
        while (nameConflicts && names.size > 0) {
            name = randomIdentifier()
            for (possibleConflict in names) {
                if (name == possibleConflict) {
                    nameConflicts = true
                    break
                }
                nameConflicts = false
            }
        }
        return name
    }

    private fun randomIdentifier(): String {
        val id = StringBuilder()
        id.append(randomNonNumeric(1))
        id.append(randomAlphaNumeric(random.nextInt(MAX_IDENTIFIER_LENGTH)))
        return id.toString()
    }

    private fun randomAlphaNumeric(length: Int): String {
        random.nextInt(10)
        return random(length, true, true, random)
    }

    private fun randomNonNumeric(length: Int): String {
        val res = StringBuilder("")
        if (length > 0) {
            res.append(random(length, true, false, random))
        }
        return res.toString()
    }

    private fun random(count: Int, letters: Boolean, numbers: Boolean, random: Random): String {
        val alpha = "abcdefghijklmnopqrstuvwxyz"
        val num = "0123456789"
        val chars = ((if (letters) alpha + alpha.uppercase() else "") + (if (numbers) num else "")).toCharArray()
        return (1..count).joinToString("") { chars[random.nextInt(chars.size - 1)].toString() }
    }

    companion object {
        private val BOOLEAN_BINARY_OPS: List<String> = mutableListOf("AND", "OR", "XOR")
        private val INTEGER_BINARY_OPS: List<String> = mutableListOf("/", "*", "-", "+", "MOD")
        private val COMPARISON_OPS: List<String> = mutableListOf("=", ">", "<", "<=", ">=")

        private const val MAX_IDENTIFIER_LENGTH = 50
        private const val MAX_ENUM_LITERALS = 10
        private const val MAX_COMMENT_LENGTH = 100
        private const val MAX_NAME_LENGTH = 50
        private const val MAX_INT = 32767

        @Throws(ExportException::class, IOException::class)
        @JvmStatic
        fun main(args: Array<String>) {
            val generator = RandomTableGenerator()
            val constraintSpec = generator.randomConstraintSpec(5000, 10, 10)
            ExporterFacade.exportSpec(
                constraintSpec, ExporterFacade.ExportFormat.XML, File(
                    "/home/bal/Projects/kit/pse/stverificationstudio/src/test" +
                            "/resources/edu/kit/iti/formal/stvs/logic/io/xml/random" +
                            "/spec_constraint_random_5000_10_10_1.xml"
                )
            )
            //System.out.println(baos.toString("utf-8"));
        }
    }
}
