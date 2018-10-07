package edu.kit.iti.formal.automation.testtables.print

import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.util.CodeWriter
import org.antlr.v4.runtime.ParserRuleContext
import java.util.*
import java.util.stream.Stream

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
data class LatexTablePrinterOptions(
        val DONT_CARE: String = "\\DONTCARE",
        val ROW_PREAMBLE: String = "\\gttrow",
        val noRepetitionLines: Boolean = false,
        var customStyFile: MutableList<String> = arrayListOf("gtt.sty")

/*  private static final String LATEX_DONTCARE = " \\dontcare ";
  private static final String LATEX_TRUE = " \\TRUE ";
  private static final String LATEX_FALSE = " \\FALSE ";
  private static final String LATEX_NEGATION = " \\neg ";
  private static final String LATEX_MOD = " \\mathrm{mod}";
  private static final String LATEX_MULT = " * ";
  private static final String LATEX_AND = " \\land ";
  private static final String LATEX_PLUS = " + ";
  private static final String LATEX_DIV = " / ";
  private static final String LATEX_INEQUAL = "\\not=";
  private static final String LATEX_XOR = " \\mathrm{xor} ";
  private static final String LATEX_OR = " \\lor ";
*/
)

val LATEX_SPECIAL_CHARS = arrayOf("_", "^", "~", "$", "%", "#", "&", "{", "}")
fun escape(s: String, chars: Array<String> = LATEX_SPECIAL_CHARS): String {
    var t = s
    for (sc in chars) {
        t = t.replace(sc, '\\' + sc)
    }
    return t
}

abstract class AbstractTablePrinter(protected val gtt: GeneralizedTestTable,
                                    protected val stream: CodeWriter) : TablePrinter {

    protected var helper : PrinterHelper
    protected var currentRow = 0

    init {
        helper = PrinterHelper(gtt, this::cellFormatter)
    }

    val input = gtt.programVariables.filter { it.isInput }
    val output = gtt.programVariables.filter { it.isOutput }
    val durations = Stack<Pair<Duration, Int>>()
    val depth = gtt.region.depth()


    protected abstract fun contentBegin()
    protected abstract fun tableBegin()
    protected abstract fun tableEnd()
    protected abstract fun contentEnd()
    protected abstract fun regionEnd()
    protected abstract fun regionBegin()
    protected abstract fun rowBegin()
    protected abstract fun rowEnd()

    protected abstract fun printGroupDuration(dur: Duration, rowSpan: Int)
    protected abstract fun printCell(v: ProgramVariable)
    protected abstract fun printRowDuration(duration: Duration)

    override fun print() {
        contentBegin()
        tableBegin()
        printRegion(gtt.region.children)
        tableEnd()
        contentEnd()
    }

    private fun printRegion(region: List<TableNode>) {
        region.forEach { o ->
            when (o) {
                is TableRow -> printStep(o)
                is Region -> {
                    regionBegin()
                    printRegion(o)
                    regionEnd()
                }
            }
        }
    }

    private fun printRegion(b: Region) {
        durations.push(b.duration to b.count())
        printRegion(b.children)
    }

    private fun printStep(s: TableRow) {
        rowBegin()
        currentRow++

        input.forEach { v -> printCell(v) }
        output.forEach { v -> printCell(v) }

        printRowDuration(s.duration)
        while (!durations.empty()) {
            val (dur, rowSpan) = durations.pop()
            printGroupDuration(dur, rowSpan)
        }
        rowEnd()
    }

    abstract fun cellFormatter(c: TestTableLanguageParser.CellContext): String
}

class LatexTablePrinter(gtt: GeneralizedTestTable,
                        stream: CodeWriter,
                        val options: LatexTablePrinterOptions = LatexTablePrinterOptions()
) : AbstractTablePrinter(gtt, stream) {
    val drawLines = LinkedHashMap<String, String>()
    val markCounter = Counter()
    val lastTikzMarkColumn = HashMap<String, Int>()

    override fun printPreamble() {
        stream.printf("\\documentclass{standalone}\n")
        options.customStyFile.joinTo(stream) { "\\usepackage{$it}\n" }
        stream.printf("\n\\begin{document}")
    }

    override fun printPostamble() {
        stream.printf("\n\\end{document}\n")
    }


    override fun contentBegin() {}

    override fun tableBegin() {

        stream.printf("\\begin{tabular}{c|%s|%s|%s}%n",
                "c".repeat(input.size),
                "c".repeat(output.size),
                "c".repeat(depth + 1))

        stream.printf("\\# & \\multicolumn{%d}{c}{\\categoryheader{Input}} & " +
                "\\multicolumn{%d}{c}{\\categoryheader{Output}} & \\coltime \\\\%n",
                input.size, output.size)

        val wrapColumnHeader = { hdr: String -> "\\variableheader{$hdr}" }

        stream.printf("  & %s &%s \\\\%n",
                input.map { it.name }
                        .map { escape(it) }
                        .map(wrapColumnHeader)
                        .reduce { a, b -> "$a & $b" },
                output.map { it.name }
                        .map { escape(it) }
                        .map(wrapColumnHeader)
                        .reduce { a, b -> "$a & $b" })

        stream.printf("\\toprule\n")
    }


    override fun tableEnd() {
        stream.printf("\\bottomrule\n\\end{tabular}\n")
    }

    override fun contentEnd() {
        stream.printf("\\begin{tikzpicture}[remember picture, overlay]\n")
        drawLines.forEach { from, to -> System.out.printf("\\drawrepetition{%s}{%s}%n", from, to) }
        stream.printf("\\end{tikzpicture}\n")
    }

    override fun regionBegin() {
        println("\\midrule")
    }

    override fun regionEnd() {
        println("\\midrule")
    }

    override fun rowBegin() {
        stream.printf("%2d", currentRow)
    }

    override fun rowEnd() {
        System.out.printf("\\\\%n")
    }

    override fun printCell(v: ProgramVariable) {
        val cell = helper.columns[v.name]?.get(currentRow - 1)!!
        stream.printf(" & %15s",
                if (options.noRepetitionLines)
                    cell.content
                else {
                    if (cell.endGroup) {
                        tikzMarkAndDraw(v.name)
                    } else if (cell.secondInGroup) {
                        tikzMark(v.name)
                    } else if (cell.inBetween) {
                        ""
                    } else {
                        cell.content
                    }
                }
        )
    }

    override fun printRowDuration(duration: Duration) {
        stream.printf(" & %15s", beautifyDuration(duration))
    }

    override fun printGroupDuration(dur: Duration, rowSpan: Int) {
        stream.printf(" & \\rowgroupduration{%d}{%s}", rowSpan, beautifyDuration(dur))
    }

    override fun cellFormatter(c: TestTableLanguageParser.CellContext): String {
        return c.accept(LatexPrinter(options))
    }

    private fun beautifyDuration(d: Duration): String =
            when (d) {
                is Duration.Omega -> "\\TIMEOMEGA"
                is Duration.ClosedInterval -> {
                    (if (d.lower == d.upper) "{${d.lower}"
                    else "[${d.lower},${d.upper}]$") + (if (d.pflag) "\\DWAIT" else "")
                }
                is Duration.OpenInterval ->
                    String.format("$\\geq%s$", d.lower) + (if (d.pflag) "\\DWAIT" else "")
            }

    private fun tikzMark(varName: String): String {
        val c = markCounter.getAndIncrement(varName)
        lastTikzMarkColumn[varName] = c
        return String.format("\\tikzmark{%s%s}", varName, c)
    }

    private fun tikzMarkAndDraw(varName: String): String {
        val c = markCounter.getAndIncrement(varName)
        if (lastTikzMarkColumn.containsKey(varName)) {
            val b = lastTikzMarkColumn[varName]
            drawLines[varName + b] = varName + c
        }
        lastTikzMarkColumn[varName] = c
        return String.format("\\tikzmark{%s%s}", varName, c)
    }
}


/**
 * @author Alexander Weigl
 * @version 1 (01.03.18)
 */
class LatexPrinter(val options: LatexTablePrinterOptions) : TestTableLanguageBaseVisitor<String>() {
    private fun latex(command: String, args: Iterable<String>): String {
        return "\\$command" + args.map { "{$it}" }.joinToString("")
    }

    private fun latex(command: String, vararg args: ParserRuleContext): String {
        return if (args.isEmpty()) {
            "\\$command"
        } else {
            latex(command, args.map { it.accept(this) })
        }
    }

    override fun visitCell(ctx: TestTableLanguageParser.CellContext): String {
        return accept(ctx.chunk()).reduce { t, u -> "$t, $u" }.orElse("")
    }

    private fun accept(ctx: Collection<ParserRuleContext>): Stream<String> {
        return ctx.stream().map { c -> c.accept(this) }
    }

    private fun oneOf(vararg ctx: ParserRuleContext?): String {
        val x = ctx.find { Objects.nonNull(it) }
        return if (x != null) x.accept(this) else ""
    }

    override fun visitChunk(ctx: TestTableLanguageParser.ChunkContext): String {
        return oneOf(ctx.constant(), ctx.interval(), ctx.expr(),
                ctx.dontcare(), ctx.singlesided(), ctx.variable())
    }

    override fun visitDontcare(ctx: TestTableLanguageParser.DontcareContext): String {
        return latex("DONTCARE")
    }

    override fun visitI(ctx: TestTableLanguageParser.IContext): String {
        return ctx.text
    }

    override fun visitConstantInt(ctx: TestTableLanguageParser.ConstantIntContext): String {
        return oneOf(ctx.i())
    }

    override fun visitConstantTrue(ctx: TestTableLanguageParser.ConstantTrueContext): String {
        return latex("TRUE")
    }

    override fun visitConstantFalse(ctx: TestTableLanguageParser.ConstantFalseContext): String {
        return latex("FALSE")
    }

    override fun visitSinglesided(ctx: TestTableLanguageParser.SinglesidedContext): String {
        return ctx.relational_operator().accept(this) + " " + ctx.expr().accept(this)
    }

    override fun visitInterval(ctx: TestTableLanguageParser.IntervalContext): String {
        return "[" + ctx.lower.accept(this) + ", " + ctx.upper.accept(this) + "]"
    }

    override fun visitRelational_operator(ctx: TestTableLanguageParser.Relational_operatorContext): String {
        when (ctx.text) {
            "<=" -> return "\\leq"
            ">=" -> return "\\geq"
            "!=" -> return "\\neg="
            else -> return ctx.text
        }
    }

    override fun visitMinus(ctx: TestTableLanguageParser.MinusContext): String {
        return "-" + ctx.sub.accept(this)
    }

    override fun visitNegation(ctx: TestTableLanguageParser.NegationContext): String {
        return latex("NEGATION", ctx.sub)
    }

    override fun visitParens(ctx: TestTableLanguageParser.ParensContext): String {
        return latex("PARENS", ctx.sub)
    }

    override fun visitCompare(ctx: TestTableLanguageParser.CompareContext): String {
        val a = TestTableLanguageLexer.VOCABULARY.getSymbolicName(ctx.op.type)
        return latex("COMPARE_$a", ctx.left, ctx.right)
    }

    override fun visitMod(ctx: TestTableLanguageParser.ModContext): String {
        return latex("MOD", ctx.left, ctx.right)
    }

    override fun visitMult(ctx: TestTableLanguageParser.MultContext): String {
        return latex("MULT", ctx.left, ctx.right)
    }

    override fun visitFunctioncall(ctx: TestTableLanguageParser.FunctioncallContext): String {
        return latex("FUNCTION", ctx.n.text, ctx.expr())
    }

    private fun latex(command: String, n: String, stream: Collection<ParserRuleContext>): String {
        val list = stream.map { a -> a.accept(this) }.toMutableList()
        list.add(0, n)
        return latex(command, list)
    }

    override fun visitLogicalAnd(ctx: TestTableLanguageParser.LogicalAndContext): String {
        return latex("LAND", ctx.left, ctx.right)
    }

    override fun visitPlus(ctx: TestTableLanguageParser.PlusContext): String {
        return latex("PLUS", ctx.left, ctx.right)
    }

    override fun visitDiv(ctx: TestTableLanguageParser.DivContext): String {
        return latex("DIV", ctx.left, ctx.right)
    }

    override fun visitInequality(ctx: TestTableLanguageParser.InequalityContext): String {
        return latex("NOTEQUAL", ctx.left, ctx.right)
    }

    override fun visitLogicalXor(ctx: TestTableLanguageParser.LogicalXorContext): String {
        return latex("XOR", ctx.left, ctx.right)
    }

    override fun visitLogicalOr(ctx: TestTableLanguageParser.LogicalOrContext): String {
        return latex("LOR", ctx.left, ctx.right)
    }

    override fun visitEquality(ctx: TestTableLanguageParser.EqualityContext): String {
        return latex("EQUAL", ctx.left, ctx.right)
    }

    override fun visitSubstract(ctx: TestTableLanguageParser.SubstractContext): String {
        return latex("SUB", ctx.left, ctx.right)
    }

    override fun visitVariable(ctx: TestTableLanguageParser.VariableContext): String {
        return escape(ctx.IDENTIFIER().symbol.text) + if (ctx.RBRACKET() != null) "[" + ctx.i().accept(this) + "]" else ""
    }

    override fun visitGuardedcommand(ctx: TestTableLanguageParser.GuardedcommandContext): String {
        throw TODO("guarded command to latex is not implemented")
    }
}