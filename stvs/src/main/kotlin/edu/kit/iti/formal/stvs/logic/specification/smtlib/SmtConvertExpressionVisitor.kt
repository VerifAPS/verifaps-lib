package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.stvs.model.common.ValidIoVariable
import edu.kit.iti.formal.stvs.model.expressions.*
import kotlin.math.max

/**
 * This class provides a visitor for an expression to convert it into a smt model.
 *
 * @author Carsten Csiky
 */
class SmtConvertExpressionVisitor(
    private val smtEncoder: SmtEncoder, private val row: Int, private val iteration: Int,
    private val column: ValidIoVariable
) : ExpressionVisitor<SExpression> {
    val constraint: SmtModel

    /**
     * Creates a visitor to convert an expression to a set of constraints.
     *
     * @param smtEncoder encoder that holds additional information about the expression that should be
     * parsed
     * @param row row, that holds the cell the visitor should convert
     * @param iteration current iteration
     * @param column column, that holds the cell the visitor should convert
     */
    init {
        val name = "|" + column.name + "_" + row + "_" + iteration + "|"

        this.constraint = SmtModel().addHeaderDefinitions(
            SList(
                "declare-const", name,
                SmtEncoder.getSmtLibVariableTypeName(column.validType)
            )
        )

        // Constrain enum bitvectors to their valid range
        column.validType.match<Any?>({ null }, { null }, { enumeration: TypeEnum? ->
            addEnumBitvectorConstraints(name, enumeration)
            null
        })
    }

    /**
     * Adds constraints to enum variables to limit the range of their representing bitvector.
     *
     * @param name Name of solver variable
     * @param enumeration Type of enumeration
     */
    private fun addEnumBitvectorConstraints(name: String, enumeration: TypeEnum?) {
        constraint.addGlobalConstrains(SList("bvsge", name, BitvectorUtils.hexFromInt(0, 4)))
        constraint.addGlobalConstrains(
            SList("bvslt", name, BitvectorUtils.hexFromInt(enumeration!!.values.size, 4))
        )
    }


    override fun visitBinaryFunction(binaryFunctionExpr: BinaryFunctionExpr): SExpression {
        val left = binaryFunctionExpr.firstArgument.takeVisitor(this)
        val right = binaryFunctionExpr.secondArgument.takeVisitor(this)

        when (binaryFunctionExpr.operation) {
            BinaryFunctionExpr.Op.NOT_EQUALS -> return SList("not", SList("=", left, right))
            else -> {
                val name = smtlibBinOperationNames[binaryFunctionExpr.operation]
                    ?: throw IllegalArgumentException(
                        "Operation " + binaryFunctionExpr.operation + " is " + "not supported"
                    )
                return SList(name, left, right)
            }
        }
    }

    override fun visitUnaryFunction(unaryFunctionExpr: UnaryFunctionExpr): SExpression {
        val argument = unaryFunctionExpr.argument!!.takeVisitor(this)
        val name = smtlibUnaryOperationNames[unaryFunctionExpr.operation]
            ?: if (unaryFunctionExpr.operation == UnaryFunctionExpr.Op.UNARY_MINUS) {
                return SList(
                    "-",
                    SAtom("0"),
                    argument
                )
            } else {
                throw IllegalArgumentException(
                    "Operation " + unaryFunctionExpr.operation + "is " + "not supported"
                )
            }

        return SList(name, argument)
    }

    override fun visitLiteral(literalExpr: LiteralExpr): SExpression {
        val literalAsString =
            literalExpr.value.match({ integer: Int -> BitvectorUtils.hexFromInt(integer, 4) },
                { bool: Boolean -> if (bool) "true" else "false" },
                { enumeration: ValueEnum? -> this.getEnumValueAsBitvector(enumeration) })
        return SAtom(literalAsString)
    }

    private fun getEnumValueAsBitvector(enumeration: ValueEnum?): String {
        return BitvectorUtils.hexFromInt(enumeration!!.type.values.indexOf(enumeration), 4)
    }

    /*
   * private String integerLiteralAsBitVector(int integer, int length){
   * 
   * }
   */
    override fun visitVariable(variableExpr: VariableExpr): SExpression {
        val variableName = variableExpr.variableName
        val variableReferenceIndex = variableExpr.getIndex()!!.orElse(0)

        // Check if variable is in getTypeForVariable
        checkNotNull(smtEncoder.getTypeForVariable(variableName)) { "Wrong Context: No variable of name '$variableName' in getTypeForVariable" }

        // is an IOVariable?
        if (smtEncoder.isIoVariable(variableName)) {
            // Do Rule (3)

            // does it reference a previous cycle? -> guarantee reference-ability

            if (variableReferenceIndex < 0) {
                constraint.addGlobalConstrains( // sum(z-1) >= max(0, alpha - i)
                    SList(
                        "bvuge", sumRowIterations(row - 1), SAtom(
                            BitvectorUtils.hexFromInt(
                                max(0.0, -(iteration + variableReferenceIndex).toDouble()).toInt(), 4
                            )
                        )
                    )
                )
            }

            // Do Rule part of Rule (I)
            // A[-v] -> A_z_(i-v)
            return SAtom(
                "|" + variableName + "_" + row + "_" + (iteration + variableReferenceIndex) + "|"
            )

            // return new SAtom(variableName);
        } else {
            return SAtom("|$variableName|")
        }
    }

    private fun sumRowIterations(j: Int): SExpression {
        val list = SList().addAll("bvadd")

        for (l in 0..j) {
            list.addAll("n_$l")
        }
        return list
    }

    companion object {
        // static maps
        private val smtlibUnaryOperationNames = mapOf(
            UnaryFunctionExpr.Op.NOT to "not",
            UnaryFunctionExpr.Op.UNARY_MINUS to "bvneg"
        )
        private val smtlibBinOperationNames = mapOf(
            BinaryFunctionExpr.Op.AND to "and",
            BinaryFunctionExpr.Op.OR to "or",
            BinaryFunctionExpr.Op.XOR to "xor",
            BinaryFunctionExpr.Op.DIVISION to "bvsdiv",
            BinaryFunctionExpr.Op.MULTIPLICATION to "bvmul",
            BinaryFunctionExpr.Op.EQUALS to "=",
            BinaryFunctionExpr.Op.GREATER_EQUALS to "bvsge",
            BinaryFunctionExpr.Op.LESS_EQUALS to "bvsle",
            BinaryFunctionExpr.Op.LESS_THAN to "bvslt",
            BinaryFunctionExpr.Op.GREATER_THAN to "bvsgt",
            BinaryFunctionExpr.Op.MINUS to "bvsub",
            BinaryFunctionExpr.Op.PLUS to "bvadd",
            BinaryFunctionExpr.Op.MODULO to "bvsmod"
        )
    }
}
