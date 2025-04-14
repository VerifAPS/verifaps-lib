package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.smt.*
import edu.kit.iti.formal.stvs.logic.specification.smtlib.BitvectorUtils.hexFromInt
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
) : ExpressionVisitor<SExpr> {
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
        val name = sym("|${column.name}_${row}_$iteration|")

        this.constraint = SmtModel().addHeaderDefinition(
            SList("declare-const", name, SmtEncoder.getSmtLibVariableTypeName(column.validType))
        )

        // Constraint enum bitvectors to their valid range
        column.validType.match({ null }, { null }, { enumeration: TypeEnum? ->
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
    private fun addEnumBitvectorConstraints(name: SSymbol, enumeration: TypeEnum?) {
        constraint.addGlobalConstraint(SList("bvsge", name, hexFromInt(0, 4)))
        constraint.addGlobalConstraint(
            SList("bvslt", name, hexFromInt(enumeration!!.values.size, 4))
        )
    }


    override fun visitBinaryFunction(binary: BinaryFunctionExpr): SExpr {
        val left = binary.firstArgument.accept(this)
        val right = binary.secondArgument.accept(this)

        when (binary.operation) {
            BinaryFunctionExpr.Op.NOT_EQUALS -> return SExprFacade.notEquals(left, right)
            else -> {
                val name = smtlibBinOperationNames[binary.operation]
                    ?: throw IllegalArgumentException(
                        "Operation " + binary.operation + " is " + "not supported"
                    )
                return SList(name, left, right)
            }
        }
    }

    override fun visitUnaryFunction(unary: UnaryFunctionExpr): SExpr {
        val argument = unary.argument.accept(this)
        val name = smtlibUnaryOperationNames[unary.operation]
            ?: if (unary.operation == UnaryFunctionExpr.Op.UNARY_MINUS) {
                return SList("-", SNumber(0), argument)
            } else {
                throw IllegalArgumentException(
                    "Operation " + unary.operation + "is " + "not supported"
                )
            }

        return SList(name, argument)
    }

    override fun visitLiteral(literal: LiteralExpr): SExpr {
        return literal.value.match(
            { hexFromInt(it, 4) },
            { sym(if (it) "true" else "false") },
            { getEnumValueAsBitvector(it) })

    }

    private fun getEnumValueAsBitvector(enumeration: ValueEnum) =
        hexFromInt(enumeration.type.values.indexOf(enumeration), 4)

    /*
   * private String integerLiteralAsBitVector(int integer, int length){
   * 
   * }
   */
    override fun visitVariable(expr: VariableExpr): SExpr {
        val variableName = expr.variableName
        val variableReferenceIndex = expr.index ?: 0

        // Check if variable is in getTypeForVariable
        checkNotNull(smtEncoder.getTypeForVariable(variableName)) { "Wrong Context: No variable of name '$variableName' in getTypeForVariable" }

        // is an IOVariable?
        if (smtEncoder.isIoVariable(variableName)) {
            // Do Rule (3)

            // does it reference a previous cycle? -> guarantee reference-ability

            if (variableReferenceIndex < 0) {
                constraint.addGlobalConstraint( // sum(z-1) >= max(0, alpha - i)
                    SList(
                        "bvuge", sumRowIterations(row - 1),
                        hexFromInt(max(0.0, -(iteration + variableReferenceIndex).toDouble()).toInt(), 4)
                    )
                )
            }

            // Do Rule part of Rule (I)
            // A[-v] -> A_z_(i-v)
            return sym("|${variableName}_${row}_${iteration + variableReferenceIndex}|")

            // return new SAtom(variableName);
        } else {
            return sym("|$variableName|")
        }
    }

    override fun visit(expr: GuardedExpression): SExpr {
        TODO("Not yet implemented")
    }

    private fun sumRowIterations(j: Int): SExpr {
        val list = SList()
        list.add(sym("bvadd"))

        for (l in 0..j) {
            list.add(sym("n_$l"))
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
