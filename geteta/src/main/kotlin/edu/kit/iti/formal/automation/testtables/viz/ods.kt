package edu.kit.iti.formal.automation.testtables.viz

import com.github.jferard.fastods.OdsFactory
import com.github.jferard.fastods.Table
import com.github.jferard.fastods.TableCell
import com.github.jferard.fastods.datastyle.DataStyle
import com.github.jferard.fastods.datastyle.createFloatStyleBuilder
import com.github.jferard.fastods.style.BorderAttribute
import com.github.jferard.fastods.style.TableCellStyle
import com.github.jferard.fastods.util.SimpleLength
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.AnyInt
import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.sfclang.getUniqueName
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.smv.CounterExample
import edu.kit.iti.formal.smv.EnumType
import edu.kit.iti.formal.smv.SMVAstDefaultVisitorNN
import edu.kit.iti.formal.smv.ast.*
import java.util.*
import java.util.logging.Logger
import kotlin.collections.HashMap

abstract class ODSWriter {
    protected val odsFactory = OdsFactory.create(Logger.getLogger(""), Locale.US)
    protected val writer = odsFactory.createWriter()
    protected val document = writer.document()
}

abstract class ODSTestTableWriter(protected val gtt: GeneralizedTestTable) : ODSWriter() {
    protected val input = gtt.programVariables.filter { it.isInput }
    protected val output = gtt.programVariables.filter { it.isOutput }
}

class ODSCounterExampleWriter constructor(
        private val counterExample: CounterExample,
        gtt: GeneralizedTestTable,
        private val mapping: Collection<Mapping>,
        var tableStyle: TableStyle = DefaultTableStyle)
    : Runnable, ODSTestTableWriter(gtt) {
    lateinit var currentTable: Table

    override fun run() = mapping.forEach { createTable(it) }

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

fun createTableWithoutProgram(gtt: GeneralizedTestTable, tableStyle: TableStyle) {
    val top = TableHeadGroup<TableHeadGroup<DebugColumn>>()

    val emptyCategory = TableHeadGroup<TableHeadGroup<DebugColumn>>()
    val pauseCategory = TableHeadGroup<TableHeadGroup<DebugColumn>>()
    val inputCategory = TableHeadGroup<TableHeadGroup<DebugColumn>>()
    val ouputCategory = TableHeadGroup<TableHeadGroup<DebugColumn>>()

    top.add("", emptyCategory)


    if (gtt.options.relational) {
        top.add("PAUSE", pauseCategory)
        top.categoryStyle["PAUSE"] = tableStyle.styleCategoryHeader

        gtt.programRuns.forEach {
            val cat = TableHeadGroup<DebugColumn>()
            val r = EmptyDebugColumn
            pauseCategory.add(it, cat)
            cat.add("", r)
        }
    }

    top.add("INPUT", inputCategory)
    top.categoryStyle["INPUT"] = tableStyle.styleCategoryHeader

    gtt.programVariables.filter { it.isInput }
            .forEach {
                val head = TableHeadGroup<DebugColumn>()
                head.add("V", ValueDebugColumn(it, RandomValueOracle))
                head.add("C", ValueDebugColumn(it, RandomValueOracle))
                inputCategory.add(it.name, ConstraintDebugColumn(it))
            }



    top.add("OUTPUT", inputCategory)
    top.categoryStyle["OUTPUT"] = tableStyle.styleCategoryHeader


    /*
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
    }*/

}

interface DebugColumn {
    fun writeCell(cell: TableCell, cindex: Int, odsDebugTable: ODSDebugTable)
}

object EmptyDebugColumn : DebugColumn {
    override fun writeCell(cell: TableCell, cindex: Int, odsDebugTable: ODSDebugTable) {}
}

object RowIdDebugColumn : DebugColumn {
    override fun writeCell(cell: TableCell, cindex: Int, odsDebugTable: ODSDebugTable) {
        val currentTableRow = odsDebugTable.unwinding[odsDebugTable.currentRow]
        cell.setStringValue(currentTableRow.id)
        //cell.setStyle(cellStyle)
    }
}

interface ProgramVariableColumn : DebugColumn {
    val programVar: ProgramVariable
}

class ValueDebugColumn(private val programVar: ProgramVariable, private val oracle: ValueOracle) : DebugColumn {
    override fun writeCell(cell: TableCell, cindex: Int, odsDebugTable: ODSDebugTable) {
        val constraint = odsDebugTable.getCurrentConstraint(programVar)
        val first = constraint.chunk(0)
        when (first) { // try to find a constant in the first chunk
            is TestTableLanguageParser.ConstantFalseContext ->
                cell.setBooleanValue(false)
            is TestTableLanguageParser.ConstantTrueContext ->
                cell.setBooleanValue(true)
            is TestTableLanguageParser.ConstantIntContext -> {
                cell.setStringValue((first as TestTableLanguageParser.ConstantIntContext).text)
            }
            else -> {
                val dt = programVar.dataType
                when (dt) {
                    is AnyInt -> cell.setFloatValue(oracle.getInteger(dt))
                    is AnyBit.BOOL -> cell.setBooleanValue(oracle.getBoolean())
                    is EnumerateType -> cell.setStringValue(oracle.getEnumValue(dt))
                    else -> cell.setStringValue("no oracle for ${dt.name}")
                }
            }
        }
    }
}

class ConstraintDebugColumn(
        private val programVar: ProgramVariable) : DebugColumn {
    override fun writeCell(cell: TableCell, cindex: Int, odsDebugTable: ODSDebugTable) {
        val constraint = odsDebugTable.currentTableRow.(programVar)
        val fml = constraint.accept(odsDebugTable.formulaPrinter)
        cell.setFormula(fml)
        //cell.setStyle()
    }
}

class ProgramOutputDebugColumn : DebugColumn {
    override fun writeCell(cell: TableCell, cindex: Int, odsDebugTable: ODSDebugTable) {
    }
}

interface ValueOracle {
    fun getInteger(dt: AnyInt): Int
    fun getEnumValue(dt: EnumerateType): String
    fun getBoolean(): Boolean
}

object RandomValueOracle : ValueOracle {
    val random = Random(2432632525234)
    override fun getInteger(dt: AnyInt): Int = random.nextInt(dt.upperBound.toInt())
    override fun getEnumValue(dt: EnumerateType) =
            dt.allowedValues.keys.take(random.nextInt(dt.allowedValues.size) - 1).last()

    override fun getBoolean() = random.nextBoolean()
}

class TableHeadGroup<T> {
    private val map = LinkedHashMap<String, MutableCollection<T>>()
    fun getCategories(): Collection<String> = map.keys
    fun getColumns(cat: String): MutableCollection<T> = map.computeIfAbsent(cat) { ArrayList() }
    fun add(cat: String, col: T) = getColumns(cat).add(col)
    val categoryStyle = HashMap<String, TableCellStyle>()
    fun getCategoryStyle(cat: String) = categoryStyle[cat]
}

class ODSDebugTable(
        gtt: GeneralizedTestTable,
        private val columns: TableHeadGroup<TableHeadGroup<DebugColumn>>,
        internal val unwinding: List<TableRow>,
        var tableStyle: TableStyle = DefaultTableStyle
) : Runnable, ODSTestTableWriter(gtt) {
    var currentTable: Table = document.addTable(getUniqueName())
    var currentRow = 2

    override fun run() {
        writeCategories()
        writeVariableColumns()
        writeBody()
    }

    protected fun writeCategories() {
        val row = currentTable.nextRow()
        val cell = row.walker

        for (cat in columns.getCategories()) {
            cell.setStringValue(cat)
            cell.setStyle(columns.getCategoryStyle(cat))
            val subs = Math.min(1, columns.getColumns(cat).size)
            cell.setColumnsSpanned(subs)
            for (i in 1..subs) cell.next()
        }
    }

    protected fun writeVariableColumns() {
        val row = currentTable.nextRow()
        val cell = row.walker
        for (cat in columns.getCategories()) {
            for (col in columns.getColumns(cat)) {
                for (v in col.getCategories()) {
                    cell.setStringValue(v)
                    cell.setStyle(col.getCategoryStyle(cat))
                    val subs = Math.min(1, col.getColumns(cat).size)
                    cell.setColumnsSpanned(subs)
                    for (i in 1..subs) cell.next()
                }
            }
        }
    }

    protected fun writeBody() = unwinding.forEach { writeRow(it) }
    protected fun writeRow(it: TableRow) {
        ++currentRow
        val cindex = 0
        val row = currentTable.nextRow()
        val cell = row.walker

        for (cat in columns.getCategories()) {
            for (col in columns.getColumns(cat)) {
                for (v in col.getCategories()) {
                    for (column in col.getColumns(v))
                        column.writeCell(cell, cindex, this)
                }
            }
        }
    }

    val currentTableRow: TableRow
        get() = unwinding[currentRow]

    private val var2column: Map<String, Int> by lazy {
        var c = 0
        val map = HashMap<String, Int>()
        for (cat in columns.getCategories()) {
            for (col in columns.getColumns(cat)) {
                for (v in col.getCategories()) {
                    for (column in col.getColumns(v))
                        if (column is ProgramVariableColumn)
                            map[column.programVar.name] = c
                    ++c
                }
            }
        }
        map
    }

    val formulaPrinter: Smv2OdsFml
        get() = Smv2OdsFml(var2column, currentRow)


    fun getCurrentConstraint(programVar: ProgramVariable) =
            currentTableRow.rawFields[programVar]!!
}


class Smv2OdsFml(val var2column: Map<String, Int>, val currentRow: Int)
    : SMVAstDefaultVisitorNN<String>() {
    override fun defaultVisit(top: SMVAst): String = ""
    override fun visit(v: SVariable) =
            if (v.name in var2column)
                ('A' + var2column[v.name]!!) + "" + (currentRow)
            else
                v.name

    override fun visit(be: SBinaryExpression): String {
        val l = be.left.accept(this)
        val r = be.right.accept(this)
        return when (be.operator) {
            SBinaryOperator.PLUS -> "$l+$r"
            SBinaryOperator.MINUS -> "$l-$r"
            SBinaryOperator.DIV -> "$l/$r"
            SBinaryOperator.MUL -> "$l*$r"
            SBinaryOperator.AND -> "AND($l,$r)"
            SBinaryOperator.OR -> "AND($l,$r)"
            SBinaryOperator.LESS_THAN -> "$l<$r"
            SBinaryOperator.LESS_EQUAL -> "$l<=$r"
            SBinaryOperator.GREATER_THAN -> "$l>$r"
            SBinaryOperator.GREATER_EQUAL -> "$l>=$r"
            SBinaryOperator.XOR -> "XOR($l,$r)"
            SBinaryOperator.XNOR -> TODO()
            SBinaryOperator.EQUAL -> "$l=$r"
            SBinaryOperator.IMPL -> "OR(NOT($l),$r)"
            SBinaryOperator.EQUIV -> "$l=$r"
            SBinaryOperator.NOT_EQUAL -> "$l<>$r"
            SBinaryOperator.MOD -> "MOD($l,$r)"
            SBinaryOperator.SHL -> TODO()
            SBinaryOperator.SHR -> TODO()
            SBinaryOperator.WORD_CONCAT -> TODO()
        }

    }

    override fun visit(ue: SUnaryExpression): String {
        val e = ue.expr.accept(this)
        return when (ue.operator) {
            SUnaryOperator.NEGATE -> "NOT($e)"
            SUnaryOperator.MINUS -> "-($e)"
        }
    }

    override fun visit(l: SLiteral): String =
            when (l.dataType) {
                is EnumType -> '"' + l.value.toString() + '"'
                else -> l.value.toString()
            }

    override fun visit(ce: SCaseExpression): String {
        return super.visit(ce)
    }
}

/*
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
*/

interface TableStyle {
    val styleRowId: TableCellStyle
    val styleRowIdHeader: TableCellStyle
    val styleCategoryHeader: TableCellStyle
    val stylePauseVariableHeader: TableCellStyle
    val styleOutputVariableHeader: TableCellStyle
    val styleInputVariableHeader: TableCellStyle
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
