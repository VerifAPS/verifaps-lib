package edu.kit.iti.formal.automation.testtables.viz

import com.github.jferard.fastods.OdsFactory
import com.github.jferard.fastods.Table
import com.github.jferard.fastods.datastyle.DataStyle
import com.github.jferard.fastods.datastyle.createFloatStyleBuilder
import com.github.jferard.fastods.style.BorderAttribute
import com.github.jferard.fastods.style.TableCellStyle
import com.github.jferard.fastods.util.SimpleLength
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.AnyInt
import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.sfclang.getUniqueName
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.smv.CounterExample
import java.util.*
import java.util.logging.Logger
import kotlin.collections.HashMap


class ODSCounterExampleWriter constructor(
        private val counterExample: CounterExample,
        private val gtt: GeneralizedTestTable,
        private val mapping: Collection<Mapping>,
        var tableStyle: TableStyle = DefaultTableStyle
) : Runnable {
    val odsFactory = OdsFactory.create(Logger.getLogger("example"), Locale.US)
    val writer = odsFactory.createWriter()
    val document = writer.document()

    lateinit var currentTable: Table

    override fun run() {
        mapping.forEach { createTable(it) }
    }


    val input = gtt.programVariables.filter { it.isInput }
    val output = gtt.programVariables.filter { it.isOutput }

    private fun createTable(m: Mapping) {
        currentTable = document.addTable(getUniqueName())
        writeHeader()
        writeCounterExample(m)
    }

    private fun writeHeader() {
        writeCategories()
        writeVariableColumns()
    }

    private fun writeCategories() {
        val row = currentTable.nextRow()
        val cell = row.walker

        cell.setStringValue("#")
        cell.setStyle(tableStyle.styleRowIdHeader)
        cell.next()

        if (gtt.options.relational) {
            //TODO
            cell.setStringValue("PAUSE")
            cell.setStyle(tableStyle.styleCategoryHeader)
            cell.setColumnsSpanned(gtt.maxProgramRun)
            cell.next()
        }

        cell.setStringValue("INPUT")
        cell.setStyle(tableStyle.styleCategoryHeader)
        cell.setColumnsSpanned(input.size)
        cell.next()

        cell.setStringValue("OUTPUT")
        cell.setStyle(tableStyle.styleCategoryHeader)
        cell.setColumnsSpanned(output.size)
        cell.next()
    }

    private fun writeVariableColumns() {
        val row = currentTable.nextRow()
        val cell = row.walker

        cell.setStringValue("")
        cell.next()

        if (gtt.options.relational) {
            gtt.programRuns.forEach {
                cell.setStringValue(it)
                cell.setStyle(tableStyle.stylePauseVariableHeader)
                cell.next()
            }
        }


        if (input.isEmpty()) {
            cell.setStringValue("")
            cell.next()
        } else {
            input.forEach {
                cell.setStringValue(it.name)
                cell.setStyle(tableStyle.styleInputVariableHeader)
                cell.next()
            }
        }
        output.forEach {
            cell.setStringValue(it.name)
            cell.setStyle(tableStyle.styleOutputVariableHeader)
            cell.next()
        }
    }

    fun writeCounterExample(map: Mapping) {
        val rowIds = map.asRowList()
        rowIds.forEachIndexed { index, rowId ->
            writeLine(index, rowId)
        }
    }

    private fun writeLine(index: Int, rowId: String) {
        val row = currentTable.nextRow()
        val cell = row.walker

        val tableRow = gtt.getTableRow(rowId)

        cell.setStringValue(tableRow?.id)
        cell.setStyle(tableStyle.styleRowId)
        cell.next()

        if (gtt.options.relational) {
            gtt.programRuns.forEach {
                cell.setStringValue(it)
                cell.setStyle(tableStyle.stylePauseVariableHeader)
                cell.next()
            }
        }

        if (input.isEmpty()) {
            cell.setStringValue("")
            cell.next()
        } else {
            input.forEach {
                //Fix input clashes
                val v = counterExample[index, it.name]
                cell.setStyle(tableStyle.styleInputValue)
                cell.setStringValue(v)
                cell.setTooltip(tableRow?.rawFields?.get(it)?.text)
                cell.next()
            }
        }
        output.forEach {
            val v = counterExample[index, it.externalVariable(gtt.programRuns).name]
            cell.setStyle(tableStyle.styleOutputValue)
            cell.setTooltip(tableRow?.rawFields?.get(it)?.text)
            cell.setStringValue(v)
            cell.next()
        }
    }
}

open class TableUnwinder(private val gtt: GeneralizedTestTable,
                         private val unwinding: Map<TableNode, Int>) {
    private val ret = ArrayList<TableRow>()
    operator fun invoke(): List<TableRow> {
        ret.clear()
        unwind(gtt.region)
        return ret.toList()
    }

    private fun unwind(tn: TableNode) =
            when (tn) {
                is Region -> unwind(tn);
                is TableRow -> unwind(tn)
            }

    private fun unwind(tr: TableRow) {
        val num = unwindingsOf(tr)
        for (i in 1..num) {
            ret.add(tr)
        }
    }

    private fun unwind(region: Region) {
        val num = unwindingsOf(region)
        for (i in 1..num) {
            region.children.forEach { unwind(it) }
        }
    }

    protected fun unwindingsOf(tn: TableNode): Int =
            unwinding.getOrDefault(tn, tn.duration.defaultUnwindings)

    private val Duration.defaultUnwindings: Int
        get() = when (this@defaultUnwindings) {
            is Duration.Omega -> 1
            is Duration.ClosedInterval -> Math.max(lower, 1)
            is Duration.OpenInterval -> Math.max(lower, 1)
        }
}

class ODSDebugTable constructor(
        private val gtt: GeneralizedTestTable,
        private val unwinding: List<TableRow>,
        var tableStyle: TableStyle = DefaultTableStyle
) : Runnable {
    val odsFactory = OdsFactory.create(Logger.getLogger("example"), Locale.US)
    val writer = odsFactory.createWriter()
    val document = writer.document()

    val input = gtt.programVariables.filter { it.isInput }
    val output = gtt.programVariables.filter { it.isOutput }

    var currentTable: Table = document.addTable(getUniqueName())

    val var2column = HashMap<String, Int>()

    override fun run() {
        writeCategories()
        writeVariableColumns()
        writeBody()
    }

    private fun writeBody() {
        //fill column map
        (input + output).forEachIndexed { i, v ->
            var2column[v.name] = 1 + i * 2
        }
        unwinding.forEach { writeRow(it) }
    }

    var currentRow = 2

    private fun writeRow(it: TableRow) {
        ++currentRow
        val row = currentTable.nextRow()
        val cell = row.walker

        cell.setStringValue(it.id)
        cell.next()

        (input + output).forEachIndexed { index, variable ->
            val dt = variable.dataType
            //TODO if constraint is a constant use it!
            val constraint = it.rawFields[variable]!!
            val first = constraint.chunk(0)
            when (first) {
                //is TestTableLanguageParser.VariableContext ->
                is TestTableLanguageParser.ConstantFalseContext ->
                    cell.setBooleanValue(false)
                is TestTableLanguageParser.ConstantTrueContext ->
                    cell.setBooleanValue(true)
                is TestTableLanguageParser.ConstantIntContext -> {
                    cell.setStringValue((first as TestTableLanguageParser.ConstantIntContext).text)
                }
                else ->
                    when (dt) {
                        is AnyInt -> cell.setFloatValue(0)
                        is AnyBit.BOOL -> cell.setBooleanValue(false)
                        is EnumerateType -> cell.setStringValue(dt.defValue)
                        else -> cell.setStringValue("")
                    }
            }
            cell.next()
            cell.setFormula(getFormulaFor(it, variable))
            cell.next()
        }
    }

    private fun getFormulaFor(it: TableRow, variable: ProgramVariable): String? {
        //        val constraint = it.inputExpr[variable.name] ?: it.outputExpr[variable.name]!!
        val constraint = it.rawFields[variable]!!
        return constraint.accept(ODSFormulaPrinter(gtt,variable.name, currentRow, var2column))
    }

    private fun writeCategories() {
        val row = currentTable.nextRow()
        val cell = row.walker

        cell.setStringValue("#")
        cell.setStyle(tableStyle.styleRowIdHeader)
        cell.next()

        if (gtt.options.relational) {
            //TODO
            cell.setStringValue("PAUSE")
            cell.setStyle(tableStyle.styleCategoryHeader)
            cell.setColumnsSpanned(gtt.maxProgramRun)
            cell.next()
        }

        cell.setStringValue("INPUT")
        cell.setStyle(tableStyle.styleCategoryHeader)
        cell.setColumnsSpanned(input.size * 2)
        cell.next()

        cell.setStringValue("OUTPUT")
        cell.setStyle(tableStyle.styleCategoryHeader)
        cell.setColumnsSpanned(output.size * 2)
        cell.next()
    }

    private fun writeVariableColumns() {
        val row = currentTable.nextRow()
        val cell = row.walker

        cell.setStringValue("")
        cell.next()

        if (gtt.options.relational) {
            gtt.programRuns.forEach {
                cell.setStringValue(it)
                cell.setStyle(tableStyle.stylePauseVariableHeader)
                cell.next()
            }
        }


        if (input.isEmpty()) {
            cell.setStringValue("")
            cell.next()
        } else {
            input.forEach {
                cell.setStringValue(it.name)
                cell.setStyle(tableStyle.styleInputVariableHeader)
                cell.setColumnsSpanned(2)
                cell.next()
                cell.next()
            }
        }
        output.forEach {
            cell.setStringValue(it.name)
            cell.setStyle(tableStyle.styleOutputVariableHeader)
            cell.setColumnsSpanned(2)
            cell.next()
            cell.next()
        }
    }

}

class ODSFormulaPrinter(
        val gtt: GeneralizedTestTable,
        val variable: String,
        val currentRow: Int,
        val var2column: Map<String, Int>)
    : TestTableLanguageBaseVisitor<String>() {
    override fun visitCell(ctx: TestTableLanguageParser.CellContext): String =
            ctx.chunk().joinToString("; ", "AND(", ")") { it.accept(this) }


    override fun visitChunk(ctx: TestTableLanguageParser.ChunkContext): String {
        if (ctx.constant() != null) {
            val constant = ctx.constant().accept(this)
            return constant + "=" + columnOf(variable, 0)
        }
        if (ctx.dontcare() != null)
            return ctx.dontcare().accept(this)
        if (ctx.interval() != null)
            return ctx.interval().accept(this)
        if (ctx.singlesided() != null)
            return ctx.singlesided().accept(this)
        if (ctx.expr() != null)
            return ctx.expr().accept(this)
        if (ctx.variable() != null) {
            val v = ctx.variable().accept(this)
            return v + "=" + columnOf(variable, 0)
        }
        throw IllegalStateException("No one of the N contexts matches")
    }

    override fun visitDontcare(ctx: TestTableLanguageParser.DontcareContext) = "TRUE()"

    override fun visitConstantInt(ctx: TestTableLanguageParser.ConstantIntContext) = ctx.text

    override fun visitConstantTrue(ctx: TestTableLanguageParser.ConstantTrueContext?) = "TRUE()"

    override fun visitConstantFalse(ctx: TestTableLanguageParser.ConstantFalseContext?) = "FALSE()"

    override fun visitSinglesided(ctx: TestTableLanguageParser.SinglesidedContext): String {
        return columnOf(variable, 0) + ctx.relational_operator().text + ctx.expr().accept(this)
    }

    private fun columnOf(variable: String, i: Int): String =
            when {
                gtt.isProgramVariable(variable) ->
                    ('A' + var2column[variable]!!) + "" + (currentRow - i)
                gtt.isConstraintVariable(variable) -> variable
                else -> "\"$variable\"" //ENUM CONSTANT
            }

    override fun visitInterval(ctx: TestTableLanguageParser.IntervalContext): String =
            "AND(" + ctx.lower.accept(this) + "<=" + columnOf(variable, 0) + "; " + columnOf(variable, 0) + ctx.upper.accept(this) + ")"

    override fun visitMinus(ctx: TestTableLanguageParser.MinusContext) = "-" + ctx.expr().accept(this)

    override fun visitNegation(ctx: TestTableLanguageParser.NegationContext) = "NOT(" + ctx.expr().accept(this) + ")"


    override fun visitParens(ctx: TestTableLanguageParser.ParensContext) = "(" + ctx.expr().accept(this) + ")"

    override fun visitCompare(ctx: TestTableLanguageParser.CompareContext) = ctx.left.accept(this) + ctx.op.text + ctx.right.accept(this)

    override fun visitMod(ctx: TestTableLanguageParser.ModContext) = "MOD(" + ctx.left.accept(this) + "," + ctx.right.accept(this) + ")"

    override fun visitMult(ctx: TestTableLanguageParser.MultContext) = ctx.left.accept(this) + "*" + ctx.right.accept(this)

    override fun visitFunctioncall(ctx: TestTableLanguageParser.FunctioncallContext) = ctx.IDENTIFIER().text +
            ctx.expr().joinToString("; ", "(", ")")
            { it.accept(this) }

    override fun visitLogicalAnd(ctx: TestTableLanguageParser.LogicalAndContext) = ctx.left.accept(this) + "AND" + ctx.right.accept(this)


    override fun visitPlus(ctx: TestTableLanguageParser.PlusContext) = ctx.left.accept(this) + "+" + ctx.right.accept(this)


    override fun visitDiv(ctx: TestTableLanguageParser.DivContext) = " DIV(" + ctx.left.accept(this) + "," + ctx.right.accept(this) + ")"

    override fun visitInequality(ctx: TestTableLanguageParser.InequalityContext) = ctx.left.accept(this) + "<>" + ctx.right.accept(this)


    override fun visitLogicalXor(ctx: TestTableLanguageParser.LogicalXorContext) = "XOR(" + ctx.left.accept(this) + ";" + ctx.right.accept(this) + ")"

    override fun visitLogicalOr(ctx: TestTableLanguageParser.LogicalOrContext) = "OR( " + ctx.left.accept(this) + "; " + ctx.right.accept(this) + ")"


    override fun visitEquality(ctx: TestTableLanguageParser.EqualityContext) = ctx.left.accept(this) + "=" + ctx.right.accept(this)


    override fun visitSubstract(ctx: TestTableLanguageParser.SubstractContext) = ctx.left.accept(this) + "-" + ctx.right.accept(this)


    override fun visitVariable(ctx: TestTableLanguageParser.VariableContext) = columnOf(ctx.IDENTIFIER().text, if (ctx.INTEGER() != null) ctx.INTEGER().text.toInt() else 0)

    override fun visitGuardedcommand(ctx: TestTableLanguageParser.GuardedcommandContext): String {
        val ret = StringBuffer()
        var i = 0
        while (i <= ctx.expr().lastIndex) {
            val g = ctx.expr(i).accept(this)
            val t = ctx.expr(i + 1).accept(this)
            ret.append("IF(")
                    .append(g).append(";")
                    .append(t).append(";")
            i += 2
        }
        ret.append("FALSE").append(")".repeat(i / 2))
        return ret.toString()
    }
}


interface TableStyle {
    val styleRowIdHeader: TableCellStyle?
    val styleCategoryHeader: TableCellStyle?
    val stylePauseVariableHeader: TableCellStyle?
    val styleOutputVariableHeader: TableCellStyle?
    val styleInputVariableHeader: TableCellStyle?
    val styleRowId: TableCellStyle?
    val styleInputValue: TableCellStyle
    val styleOutputValue: TableCellStyle
}

object DefaultTableStyle : TableStyle {
    val EMPTY = TableCellStyle.DEFAULT_CELL_STYLE
    override var styleRowId: TableCellStyle = EMPTY
    override var stylePauseVariableHeader: TableCellStyle = EMPTY

    val intStyle: DataStyle = createFloatStyleBuilder("custom-int-datastyle", Locale.getDefault())
            .decimalPlaces(8).groupThousands(true).build()


    var styleValues = TableCellStyle.builder("values")
            .build()
    override var styleOutputValue = TableCellStyle.builder("values output")
            .parentCellStyle(styleValues).build()
    override val styleInputValue = TableCellStyle.builder("values input")
            .parentCellStyle(styleValues).build()

    override var styleCategoryHeader = TableCellStyle.builder("category header")
            .backgroundColor("#ff00ff")
            .fontWeightBold()
            .textAlign(TableCellStyle.Align.CENTER)
            .build()

    var styleVariableHeader = TableCellStyle.builder("variable header")
            .backgroundColor("#cccccc")
            .fontWeightBold()
            .textAlign(TableCellStyle.Align.CENTER)
            .borderBottom(SimpleLength.pt(1.0), "#000000", BorderAttribute.Style.SOLID)
            .build()

    override val styleInputVariableHeader: TableCellStyle = TableCellStyle.builder("variable input header")
            .parentCellStyle(styleVariableHeader)
            .build()

    override val styleOutputVariableHeader = TableCellStyle.builder("variable output header")
            .parentCellStyle(styleVariableHeader)
            .build()

    override val styleRowIdHeader: TableCellStyle = TableCellStyle.builder("variable rowid header")
            .parentCellStyle(styleVariableHeader)
            .build()

    val styleRowTimeHeader: TableCellStyle = TableCellStyle.builder("variable time header")
            .parentCellStyle(styleVariableHeader)
            .build()
}
