package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.automation.datatypes.UINT
import edu.kit.iti.formal.automation.smt.Smv2SMTVisitor
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.algorithms.StateReachability
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.Duration
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.ProgramVariable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.smt.SExpr
import edu.kit.iti.formal.smt.SInteger
import edu.kit.iti.formal.smt.SList
import edu.kit.iti.formal.smt.SSymbol
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*

class SmtEncoder(
        private val traceLength: Int,
        private val maxDurations: HashMap<String, Int>,
        private val gtt: GeneralizedTestTable) {
    val model = SmtModel()

    val reachability = StateReachability(gtt.region)
    val row2Id = hashMapOf<TableRow, Int>()

    init {
        gtt.region.flat().forEachIndexed { index, tableRow -> row2Id[tableRow] = index }

        createFreeVariables()
        encodeRowTransitionFunction()
        createRowSelectors()
        createCellVariables()

        defineDurationBounds()
        unrollRowsToConstraints()
        connectBackwardReferences()
    }

    private fun encodeRowTransitionFunction() {
        "(define-fun trans ((from Int) (to Int)) Bool" +
                ""
    }

    private lateinit var cycleRows: List<SSymbol>
    private fun createRowSelectors() {
        val rows = gtt.region.flat()
        cycleRows = (1..traceLength).map { i ->
            SSymbol("cycle_row_$i").also {
                model.declare(it.text, UINT)
            }
        }

        cycleRows.zipWithNext().forEach { (a, b) ->
            model.assert(SList("trans", a, b))
        }
    }

    private fun createCellVariables() {
        for (i in 1..traceLength) {
            for (v in gtt.programVariables) {
                val s = cellOf(v, i)
                model.declare(s.text, v.dataType)
            }
        }
    }

    //(1)
    private fun createFreeVariables() {
        gtt.constraintVariables.forEach { v ->
            model.declare(v.name, v.dataType)
            v.constraint?.let {
                model.assert(translate(v.name, it))
            }
        }
    }

    //(2)
    private fun defineDurationBounds() {
        val rows = gtt.region.flat()
        rows.forEach { row ->
            val cnt = counterOf(row)
            model.declare(cnt.text, UINT)
            val duration = row.duration

            when (duration) {
                is Duration.Omega -> TODO()
                is Duration.ClosedInterval -> {
                    model.assert(SList("bvuge", cnt, model.bvOf(duration.lower, UINT.bitLength)))
                    model.assert(SList("bvule", cnt, model.bvOf(duration.upper, UINT.bitLength)))
                }
                is Duration.OpenInterval -> {
                    model.assert(SList("bvuge", cnt, model.bvOf(duration.lower, UINT.bitLength)))
                }
            }
        }
    }

    /**
     * This connects backward references by aggregating all possible backward references relative to
     * the row before they appeared.
     */
    private fun connectBackwardReferences() {
        for (v in gtt.programVariables) {
            // Iterate over Rows
            for (row in gtt.region.flat()) {
                row.constraintOf(v)?.let {
                    declareCellVariable(v, row, it)
                }
            }
        }
    }

    private fun declareCellVariable(v: ProgramVariable, cycle: Int, expr: SMVExpr) {
        // cascade for cycleRow
        val cellSym = cellOf(v, row)
    }

    private fun cellOf(v: ProgramVariable, cycle: Int) = SSymbol("cell_${cycle}_${v.name}")

    private fun translate(variable: String, constraint: TestTableLanguageParser.CellContext) {
        val smv = GetetaFacade.exprToSMV(constraint, SVariable(variable), 0, gtt.parseContext)
        val smt = smv.accept(Smv2SMTVisitor(fnTranslator, dtTranslator))
        return smt
    }

    fun counterOf(row: TableRow) = SSymbol("${row.id}_cnt")
    fun nameOf(v: ProgramVariable, tableRow: Int, iter: Int) = "|${v.name}_${tableRow}_$iter|"

    inner class SmtConvertExpressionVisitor(
            private val currentTableRow: Int,
            private val rowIteration: Int,
            private val column: ProgramVariable)
        : TestTableLanguageBaseVisitor<Sexp>() {

        val name = nameOf(column, currentTableRow, rowIteration)

        init {
            model.declareConst(name, typeOf(column))
            // Constrain enum bitvectors to their valid range
            column.getValidType().match({ null }, { null }, { enumeration ->
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
        private fun addEnumBitvectorConstraints(name: String, enumeration: TypeEnum) {
            model.assert("(bvsge $name ${BitvectorUtils.hexFromInt(0, 4)})")
            model.assert("(bvslt $name, name, BitvectorUtils.hexFromInt(enumeration.getValues().size(), 4)))
        }


        fun visitBinaryFunction(binaryFunctionExpr: BinaryFunctionExpr): SExpression {
            val left = binaryFunctionExpr.getFirstArgument().takeVisitor(this@SmtConvertExpressionVisitor)
            val right = binaryFunctionExpr.getSecondArgument().takeVisitor(this@SmtConvertExpressionVisitor)

            when (binaryFunctionExpr.getOperation()) {
                NOT_EQUALS -> return SList("not", SList("=", left, right))
                else -> {
                    val name = smtlibBinOperationNames[binaryFunctionExpr.getOperation()]
                            ?: throw IllegalArgumentException(
                                    "Operation " + binaryFunctionExpr.getOperation() + " is " + "not supported")
                    return SList(name, left, right)
                }
            }
        }

        fun visitUnaryFunction(unaryFunctionExpr: UnaryFunctionExpr): SExpression {
            val argument = unaryFunctionExpr.getArgument().takeVisitor(this)
            val name = smtlibUnaryOperationNames[unaryFunctionExpr.getOperation()]
                    ?: return if (unaryFunctionExpr.getOperation() === UnaryFunctionExpr.Op.UNARY_MINUS) {
                        SList("-", SAtom("0"), argument)
                    } else {
                        throw IllegalArgumentException(
                                "Operation " + unaryFunctionExpr.getOperation() + "is " + "not supported")
                    }

            return SList(name, argument)
        }

        fun visitLiteral(literalExpr: LiteralExpr): SExpression {
            val literalAsString = literalExpr.getValue().match({ integer -> BitvectorUtils.hexFromInt(integer, 4) },
                    { bool -> if (bool) "true" else "false" }, ???({ this.getEnumValueAsBitvector(it) }))
            return SAtom(literalAsString)
        }

        private fun getEnumValueAsBitvector(enumeration: ValueEnum): String {
            return BitvectorUtils.hexFromInt(enumeration.getType().getValues().indexOf(enumeration), 4)
        }

        /*
       * private String integerLiteralAsBitVector(int integer, int length){
       *
       * }
       */

        fun visitVariable(variableExpr: VariableExpr): SExpression {
            val variableName = variableExpr.getVariableName()
            val variableReferenceIndex = variableExpr.getIndex().orElse(0)

            // Check if variable is in getTypeForVariable
            if (smtEncoder.getTypeForVariable(variableName) == null) {
                throw IllegalStateException(
                        "Wrong Context: No variable of name '$variableName' in getTypeForVariable")
            }

            // is an IOVariable?
            if (smtEncoder.isIoVariable(variableName)) {
                // Do Rule (3)

                // does it reference a previous cycle? -> guarantee reference-ability
                if (variableReferenceIndex < 0) {
                    constraint.addGlobalConstrains(
                            // sum(z-1) >= max(0, alpha - i)
                            SList("bvuge", sumRowIterations(currentTableRow - 1), SAtom(
                                    BitvectorUtils.hexFromInt(Math.max(0, -(rowIteration + variableReferenceIndex!!)), 4))))
                }

                // Do Rule part of Rule (I)
                // A[-v] -> A_z_(i-v)
                return SAtom(
                        "|" + variableName + "_" + currentTableRow + "_" + (rowIteration + variableReferenceIndex!!) + "|")

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
            /*private val smtlibUnaryOperationNames = object : HashMap<UnaryFunctionExpr.Op, String>() {
                init {
                    put(UnaryFunctionExpr.Op.NOT, "not")
                    put(UnaryFunctionExpr.Op.UNARY_MINUS, "bvneg")
                }
            }*/

/*                    put(BinaryFunctionExpr.Op.AND, "and")
                    put(BinaryFunctionExpr.Op.OR, "or")
                    put(BinaryFunctionExpr.Op.XOR, "xor")
                    put(BinaryFunctionExpr.Op.DIVISION, "bvsdiv")
                    put(BinaryFunctionExpr.Op.MULTIPLICATION, "bvmul")
                    put(BinaryFunctionExpr.Op.EQUALS, "=")
                    put(BinaryFunctionExpr.Op.GREATER_EQUALS, "bvsge")
                    put(BinaryFunctionExpr.Op.LESS_EQUALS, "bvsle")
                    put(BinaryFunctionExpr.Op.LESS_THAN, "bvslt")
                    put(BinaryFunctionExpr.Op.GREATER_THAN, "bvsgt")
                    put(BinaryFunctionExpr.Op.MINUS, "bvsub")
                    put(BinaryFunctionExpr.Op.PLUS, "bvadd")
                    put(BinaryFunctionExpr.Op.MODULO, "bvsmod")
                    */
        }
    }
}

class TblExprToSExpr : TestTableLanguageBaseVisitor<SExpr>() {
    override fun visitCell(ctx: TestTableLanguageParser.CellContext) = SList("and", ctx.chunk().map { it.accept(this) })

    override fun visitDontcare(ctx: TestTableLanguageParser.DontcareContext) = SSymbol("true")

    override fun visitI(ctx: TestTableLanguageParser.IContext) = SInteger(ctx.INTEGER().text.toBigInteger())

    override fun visitConstantTrue(ctx: TestTableLanguageParser.ConstantTrueContext) = SSymbol("true")

    override fun visitConstantFalse(ctx: TestTableLanguageParser.ConstantFalseContext) = SSymbol("false")

    override fun visitSinglesided(ctx: TestTableLanguageParser.SinglesidedContext) = SList(ctx.relational_operator().text, variable, ctx.expr().accept(this))

    override fun visitInterval(ctx: TestTableLanguageParser.IntervalContext): SExpr =
            SList("and", SList(">=", variable, ctx.lower.accept(this)),
                    SList("<=", variable, ctx.upper.accept(this)))

    override fun visitMinus(ctx: TestTableLanguageParser.MinusContext) = SList("bvneg", ctx.expr().accept(this))

    override fun visitNegation(ctx: TestTableLanguageParser.NegationContext) = SList("not", ctx.expr().accept(this))

    override fun visitCompare(ctx: TestTableLanguageParser.CompareContext?) = binop(ctx.op.text, ctx.left, ctx.right)

    private fun binop(text: String,
                      left: TestTableLanguageParser.ExprContext,
                      right: TestTableLanguageParser.ExprContext) = SList(text, left.accept(this), right.accept(right))

    override fun visitMod(ctx: TestTableLanguageParser.ModContext) = binop("bvmod", ctx.left, ctx.right)

    override fun visitMult(ctx: TestTableLanguageParser.MultContext?) = binop("bvmult", ctx.left, ctx.right)

    override fun visitFunctioncall(ctx: TestTableLanguageParser.FunctioncallContext?): SExpr {

    }

    override fun visitLogicalAnd(ctx: TestTableLanguageParser.LogicalAndContext?) = binop("and", ctx.left, ctx.right)
    override fun visitPlus(ctx: TestTableLanguageParser.PlusContext?) = binop("bvadd", ctx.left, ctx.right)

    override fun visitDiv(ctx: TestTableLanguageParser.DivContext?) = binop("bvdiv", ctx.left, ctx.right)

    override fun visitInequality(ctx: TestTableLanguageParser.InequalityContext) = binop("bvdiv", ctx.left, ctx.right)

    override fun visitLogicalXor(ctx: TestTableLanguageParser.LogicalXorContext) = binop("distinct", ctx.left, ctx.right)

    override fun visitLogicalOr(ctx: TestTableLanguageParser.LogicalOrContext) = binop("or", ctx.left, ctx.right)

    override fun visitEquality(ctx: TestTableLanguageParser.EqualityContext) = binop("=", ctx.left, ctx.right)

    override fun visitSubstract(ctx: TestTableLanguageParser.SubstractContext) = binop("bvsub", ctx.left, ctx.right)

    override fun visitVariable(ctx: TestTableLanguageParser.VariableContext) = SSymbol(ctx.name.text)

    override fun visitGuardedcommand(ctx: TestTableLanguageParser.GuardedcommandContext?): SExpr {
        return super.visitGuardedcommand(ctx)
    }
}