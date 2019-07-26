package edu.kit.iti.formal.automation.testtables.smtconcrete

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.testtables.builder.SMVConstructionModel
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.TableRow
import edu.kit.iti.formal.automation.testtables.model.automata.AutomatonState
import edu.kit.iti.formal.smt.*
import edu.kit.iti.formal.smt.SExprFacade.sexpr
import edu.kit.iti.formal.smv.EnumType
import kotlin.math.log

interface IecToSmtDataTypeTranslator {
    fun translate(dt: Any): SmtType
}

class DefaultIecToSmtDataTypeTranslator(val useBv: Boolean) : IecToSmtDataTypeTranslator {
    val map = HashMap<Any, SmtType>()

    init {
        map[AnyBit.BOOL] = SmtBoolType
        map[AnyBit.BYTE] = SmtBitvectorType(8)
        map[AnyBit.WORD] = SmtBitvectorType(16)
        map[AnyBit.DWORD] = SmtBitvectorType(32)
        map[AnyBit.LWORD] = SmtBitvectorType(64)

        if (useBv) {
            map[INT] = SmtBitvectorType(16)
            map[UINT] = SmtBitvectorType(16)
            map[SINT] = SmtBitvectorType(8)
            map[USINT] = SmtBitvectorType(8)
            map[DINT] = SmtBitvectorType(32)
            map[LINT] = SmtBitvectorType(64)
            map[UDINT] = SmtBitvectorType(32)
            map[ULINT] = SmtBitvectorType(64)
        } else {
            map[INT] = SmtIntType
            map[UINT] = SmtIntType
            map[SINT] = SmtIntType
            map[USINT] = SmtIntType
            map[DINT] = SmtIntType
            map[LINT] = SmtIntType
            map[UDINT] = SmtIntType
            map[ULINT] = SmtIntType
        }
    }

    var enumType: SmtEnumType = SmtEnumType("emptyenum", listOf())
    override fun translate(dt: Any): SmtType {
        return if (dt is EnumerateType)
            if (useBv) return map[INT]!!
            else enumType
        else map[dt] ?: throw IllegalStateException("Undefined translation for $dt")
    }
}


class SmtEncoder(
        val gtt: GeneralizedTestTable,
        val smvModel: SMVConstructionModel,
        val traceLength: Int) {

    val model = SmtModel()
    val row2Id = hashMapOf<TableRow, Int>()
    val rows = gtt.region.flat()
    val typeTranslator: IecToSmtDataTypeTranslator

    private val succFn = SSymbol("succ")
    private val typeState = SSymbol("State")
    private val programVar = gtt.programVariables.map { it.name }.toSet()
    private val typeSEnum: SmtEnumType
    val bits = 1 + (log(traceLength.toDouble(), 10.0)).toInt()

    init {
        val d = DefaultIecToSmtDataTypeTranslator(false)
        typeTranslator = d
        val enumValues = (smvModel.superEnumType as EnumType).values
        typeSEnum = SmtEnumType("SuperEnum", enumValues)
        d.enumType = typeSEnum

        rows.forEachIndexed { index, tableRow -> row2Id[tableRow] = index }
    }

    fun run() {
        createDataType()
        createFreeVariables()
        encodeRowTransitionFunction()
        createRowSelectors()
        defineVariableTraces()
        createRowConstraints()

        createTimeToRowBinding()

        //defineDurationBounds()
        //unrollRowsToConstraints()
        //connectBackwardReferences()
    }

    private fun createTimeToRowBinding() {
        creatRConstraint()

        val eq = smvModel.automaton.initialStates.map {
            sexpr("=", sexpr(symCycleRow, 0), it.name)
        }
        model.assert(SList("or", eq))

        (0 until traceLength).forEach { i ->
            model.assert(sexpr("rconstraint", sexpr(symCycleRow, i)))
        }
    }

    private fun creatRConstraint() {
        val map = arrayListOf<Pair<SExpr, SExpr>>()
        smvModel.automaton.rowStates.forEach { (row, state) ->
            state.forEach {
                val k = sexpr("=", sexpr(symCycleRow, "i"), SSymbol(it.name))
                val v = sexpr(String.format("constraints_row_${row.id}"), "i")
                map.add(k to v)
            }
        }
        val k = sexpr("=", sexpr(symCycleRow, "i"), SSymbol(smvModel.automaton.stateSentinel.name))
        val v = SSymbol("true")
        map.add(k to v)
        val body = map.foldRight(SSymbol("false")) { (g, c), acc: SExpr ->
            sexpr("ite", g, c, acc)
        }
        /*
            (let ((c (cycle i)))
                (ite (= c row1) (constraint_row_01 i)
                    (ite (= c row2) (constraint_row_02 i)
                        false)))
        */

        model.file.add(sexpr("define-fun", "rconstraint",
                SList.singleton(sexpr("i", "Int")),
                SmtBoolType.type, body))
    }

    fun createRowConstraints() {
        /*val sig = SList()
        gtt.programVariables.forEach {
            sig.add(sexpr(it.name, typeTranslator.translate(it.dataType).type))
        }*/
        rows.forEach { createRowConstraints(it) }
    }

    fun createRowConstraints(it: TableRow) {
        val body = it.rawFields.map { (name, expr) ->
            expr!!.accept(TblExprToSExpr(name.name, programVar, "i"))
        }

        model.file.add(
                sexpr("define-fun", "constraints_row_${it.id}",
                        SList.singleton(sexpr("i", SmtIntType.type)), SmtBoolType.type,
                        SList("and", body)))
    }


    /**(0)
     * (declare-datatypes () ((BoolT True False Bot)))
     */
    fun createDataType() {
        val defState = SList(typeState)
        val states: MutableList<AutomatonState> = smvModel.automaton.rowStates.values.flatten().toMutableList()
        states.add(smvModel.automaton.stateSentinel)
        states.sortedBy { it.name }.forEach { defState.add(SSymbol(it.name)) }
        model.file.add(sexpr("declare-datatypes", SList(), sexpr(defState)))
        model.file.add(typeSEnum.declaration)
    }


    //(1)
    private fun createFreeVariables() {
        gtt.constraintVariables.forEach { v ->
            model.file.add(sexpr(v.name, typeTranslator.translate(v.dataType).type))
            v.constraint?.let {
                val s = it.accept(TblExprToSExpr(v.name, programVar))
                model.assert(s)
            }
        }
    }

    /**
    ```
    (define-fun succ ((from Int) (to Int)) Bool
    (or (and (= from X) (= to Y))
    ..))
     */
    private fun encodeRowTransitionFunction() {
        val body = sexpr("or")
        smvModel.automaton.transitions
                .filter {
                    it.to != smvModel.automaton.stateError
                }
                .forEach {
                    val from = SSymbol(it.from.name)
                    val to = SSymbol(it.to.name)
                    body.add(sexpr("and",
                            sexpr("=", "from", from),
                            sexpr("=", "to", to)))
                }
        model.file.add(sexpr(
                "define-fun", succFn, sexpr(sexpr("from", typeState), sexpr("to", typeState)), "Bool",
                body))
    }


    val symCycleRow = SSymbol("cyclerow")
    private fun createRowSelectors() {
        model.file.add(
                sexpr("declare-fun", symCycleRow,
                        sexpr("Int"), typeState))

        val row = (0 until traceLength)
        row.zipWithNext().forEach { (a, b) ->
            model.assert(sexpr(succFn, sexpr(symCycleRow, a), sexpr(symCycleRow, b)))
        }
    }

    private fun defineVariableTraces() {
        for (v in gtt.programVariables) {
            val defVar = sexpr("declare-fun", v.name,
                    SList.singleton(sexpr("i", "Int")),
                    model.dtTranslator.translate(model.typeTranslator.translate(v.dataType))
            )
            model.file.add(defVar)
        }
    }


//fun counterOf(row: TableRow) = SSymbol("${row.id}_cnt")
//fun nameOf(v: ProgramVariable, tableRow: Int, iter: Int) = "|${v.name}_${tableRow}_$iter|"
}

class TblExprToSExpr(columnVar: String,
                     val programVar: Set<String>,
                     val access: String? = null)
    : TestTableLanguageBaseVisitor<SExpr>() {

    val translation: (String) -> String = { it }

    private val variable: SExpr = if (access == null) SSymbol(columnVar) else sexpr(columnVar, access)


    override fun visitCell(ctx: TestTableLanguageParser.CellContext) =
            when {
                ctx.chunk().size == 1 -> ctx.chunk(0).accept(this)
                ctx.chunk().size == 0 -> SSymbol("true")
                else -> SList("and", ctx.chunk().map { it.accept(this) })
            }

    override fun visitDontcare(ctx: TestTableLanguageParser.DontcareContext) = SSymbol("true")

    override fun visitI(ctx: TestTableLanguageParser.IContext) = SInteger(ctx.INTEGER().text.toBigInteger())

    override fun visitConstantTrue(ctx: TestTableLanguageParser.ConstantTrueContext) = SSymbol("true")

    override fun visitConstantFalse(ctx: TestTableLanguageParser.ConstantFalseContext) = SSymbol("false")

    override fun visitSinglesided(ctx: TestTableLanguageParser.SinglesidedContext) = SList(translation(ctx.relational_operator().text), variable, ctx.expr().accept(this))

    override fun visitInterval(ctx: TestTableLanguageParser.IntervalContext): SExpr =
            SList("and", SList(">=", variable, ctx.lower.accept(this)),
                    SList("<=", variable, ctx.upper.accept(this)))

    override fun visitMinus(ctx: TestTableLanguageParser.MinusContext) = SList("bvneg", ctx.expr().accept(this))

    override fun visitNegation(ctx: TestTableLanguageParser.NegationContext) = SList("not", ctx.expr().accept(this))

    override fun visitCompare(ctx: TestTableLanguageParser.CompareContext) = binop(ctx.op.text, ctx.left, ctx.right)

    override fun visitCvariable(ctx: TestTableLanguageParser.CvariableContext): SExpr {
        return sexpr("=", variable, ctx.variable().accept(this))
    }

    override fun visitCconstant(ctx: TestTableLanguageParser.CconstantContext): SExpr {
        return sexpr("=", ctx.constant().accept(this))
    }

    private fun binop(text: String,
                      left: TestTableLanguageParser.ExprContext,
                      right: TestTableLanguageParser.ExprContext) = SList(text, left.accept(this), right.accept(this))

    override fun visitMod(ctx: TestTableLanguageParser.ModContext) = binop("bvmod", ctx.left, ctx.right)

    override fun visitMult(ctx: TestTableLanguageParser.MultContext) = binop("bvmult", ctx.left, ctx.right)

    override fun visitFunctioncall(ctx: TestTableLanguageParser.FunctioncallContext): SExpr =
            SList(ctx.IDENTIFIER().text, ctx.expr().map { it.accept(this) })

    override fun visitLogicalAnd(ctx: TestTableLanguageParser.LogicalAndContext) = binop("and", ctx.left, ctx.right)

    override fun visitPlus(ctx: TestTableLanguageParser.PlusContext) = binop("bvadd", ctx.left, ctx.right)

    override fun visitDiv(ctx: TestTableLanguageParser.DivContext) = binop("bvdiv", ctx.left, ctx.right)

    override fun visitInequality(ctx: TestTableLanguageParser.InequalityContext) = binop("bvdiv", ctx.left, ctx.right)

    override fun visitLogicalXor(ctx: TestTableLanguageParser.LogicalXorContext) = binop("distinct", ctx.left, ctx.right)

    override fun visitLogicalOr(ctx: TestTableLanguageParser.LogicalOrContext) = binop("or", ctx.left, ctx.right)

    override fun visitEquality(ctx: TestTableLanguageParser.EqualityContext) = binop("=", ctx.left, ctx.right)

    override fun visitSubstract(ctx: TestTableLanguageParser.SubstractContext) = binop("bvsub", ctx.left, ctx.right)

    override fun visitVariable(ctx: TestTableLanguageParser.VariableContext) =
            if (ctx.name.text in programVar)
                if (access != null)
                    sexpr(ctx.name.text, access)
                else
                    SSymbol(ctx.name.text)
            else
                SSymbol(ctx.name.text)

    override fun visitGuardedcommand(ctx: TestTableLanguageParser.GuardedcommandContext?): SExpr {
        return super.visitGuardedcommand(ctx)
    }
}
