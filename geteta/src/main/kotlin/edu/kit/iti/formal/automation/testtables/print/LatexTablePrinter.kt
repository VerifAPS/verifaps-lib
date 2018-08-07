package edu.kit.iti.formal.automation.testtables.print

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.options.option
import edu.kit.iti.formal.automation.st.util.Tuple
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.io.TableReader
import edu.kit.iti.formal.automation.testtables.model.*
import org.antlr.v4.runtime.ParserRuleContext
import org.w3c.dom.Element
import java.io.PrintWriter
import java.io.StringWriter
import java.util.*
import java.util.stream.Stream

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
class LatexTablePrinter(val gtt: GeneralizedTestTable) : CliktCommand() {
    val format by option()

    var backend = StringWriter()
    var stream: PrintWriter = PrintWriter(backend)

    val FILE_PREAMBLE = """
    \\documentclass{standalone}
    \\usepackage{gtt}
    """.trimIndent()

    val DONT_CARE = "\\DONTCARE"
    val ROW_PREAMBLE = "\\gttrow"
    var customStyFile: MutableList<String> = arrayListOf("gtt.sty")


    private var currentRow = 0

    val input = gtt.programVariables.filter { it.isInput }
    val output = gtt.programVariables.filter { it.isOutput }
    val durations = Stack<Tuple<Duration, Int>>()
    val cache = HashMap<String, String>()
    val drawLines = LinkedHashMap<String, String>()
    val markCounter = Counter()
    val lastTikzMarkColumn = HashMap<String, Int>()
    val specialChars = listOf("_", "^", "~", "$", "%", "#", "&", "{", "}")
    val totalNumSteps = gtt.region.count()
    val columns = LinkedHashMap<String, ArrayList<String>>()
    val depth = gtt.region.depth()

    public override fun run() {
        fillColumns()

        stream.write(FILE_PREAMBLE)
        customStyFile.joinTo(stream) { "\\usepackage{$customStyFile}\n" }
        stream.write("\\begin{document}\n")

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

        stream.println("\\toprule")

        printRegionLatex(gtt.region.children)

        stream.printf("\\bottomrule\n\\end{tabular}%n")

        stream.println("\\begin{tikzpicture}[remember picture, overlay]")
        drawLines.forEach { from, to -> System.out.printf("\\drawrepetition{%s}{%s}%n", from, to) }
        stream.println("\\end{tikzpicture}")
        stream.println("\\end{document}")
    }

    private fun fillColumns() {
        gtt.programVariables.forEach { columns[it.name] = ArrayList() }

        //prefill
        gtt.region.flat().forEach { s ->
            s.rawFields.forEach { k, v ->
                columns[k.name]?.add(parseAndSafePrint(v))
            }
        }

        //simplify
        columns.forEach { k, v ->
            if (v[0].isEmpty())
                v[0] = "-"

            var i = 0
            while (i < v.size - 1) {
                var j = i + 1
                // delete any cell contents, that is same as i
                while (j < v.size && (v[i] == v[j] || v[j].isEmpty())) {
                    v[j] = ""
                    j++
                }

                if (j == i + 2) {//one empty cell
                    v[i + 1] = "\\singlecopy{" + v[i] + "}"
                } else if (j > i + 2) {//more than one empty
                    v[i + 1] = tikzMark(k)
                    v[j - 1] = tikzMarkAndDraw(k)
                }
                i = j
            }
        }
    }

    private fun parseAndSafePrint(ctx: TestTableLanguageParser.CellContext?): String {
        if (ctx == null) return ""
        val latexPrinter = LatexPrinter()
        return ctx.accept(latexPrinter)
    }

    public fun escape(s: String): String {
        var t = s
        for (sc in specialChars) {
            t = t.replace(sc, '\\' + sc)
        }
        return t
    }

    private fun printRegionLatex(region: List<TableNode>) {
        for (o in region) {
            if (o is State) {
                printStep(o)
            }
            if (o is Region) {
                println("\\midrule")
                printRegionLatex(o)
                println("\\midrule")
            }
        }
    }

    private fun printRegionLatex(b: Region) {
        durations.push(Tuple.make(b.duration, b.count()))
        printRegionLatex(b.children)
    }

    private fun printStep(s: State) {
        System.out.printf("%2d", currentRow++)
        //List<Element> any = s.getAny().stream().map(Element.class::cast).collect(Collectors.toList());

        input!!.forEach { v -> System.out.printf(" & %15s", columns[v.name]?.get(currentRow - 1)) }

        output!!.forEach { v -> System.out.printf(" & %15s", columns[v.name]?.get(currentRow - 1)) }

        System.out.printf(" & %15s", beautifyDuration(s.duration))
        while (!durations.empty()) {
            val d = durations.pop()
            System.out.printf(" & \\rowgroupduration{%d}{%s}", d.b, beautifyDuration(d.a))
        }
        System.out.printf("\\\\%n")
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

    private operator fun get(s: List<Element>, varName: String, pos: Int, lastRow: Boolean): String {
        val value = TableReader.get(s, varName, pos)
        val cacheValue = cache[varName]
        if (value != null) { //value defined
            cache[varName] = value //save into cache
            return if (value == cacheValue) if (lastRow) tikzMarkAndDraw(varName) else "" else tikzMarkAndDraw(varName) + escape(value)
            //else return new value.
        }
        if (cacheValue == null) {
            cache[varName] = "-"
            return DONT_CARE + tikzMark(varName) //first row
        } else {
            return if (lastRow) tikzMarkAndDraw(varName) else ""
        }
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


    class Counter {
        private val counter = LinkedHashMap<String, Int>()

        fun peek(s: String): Int =
                counter.computeIfAbsent(s) { _ -> 0 }

        fun getAndIncrement(s: String): Int {
            val peek = peek(s)
            counter[s] = peek + 1
            return peek
        }
    }


    /**
     * @author Alexander Weigl
     * @version 1 (01.03.18)
     */
    inner class LatexPrinter : TestTableLanguageBaseVisitor<String>() {
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
        fun latex(command: String, args: Iterable<String>): String {
            return "\\$command" + args.map { "{$it}" }.joinToString("")
        }

        fun latex(command: String, vararg args: ParserRuleContext): String {
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
}