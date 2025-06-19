/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.automation.testtables.print

import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParserBaseVisitor
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
    var customStyFile: MutableList<String> = arrayListOf("gtt.sty"),

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

class LatexTablePrinter(
    gtt: GeneralizedTestTable,
    stream: CodeWriter,
    val options: LatexTablePrinterOptions = LatexTablePrinterOptions(),
) : AbstractTablePrinter(gtt, stream) {
    val drawLines = LinkedHashMap<String, String>()
    val markCounter = Counter()
    val lastTikzMarkColumn = HashMap<String, Int>()

    init {
        init()
    }

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
        stream.printf(
            "\\begin{tabular}{c|%s|%s|%s}%n",
            "c".repeat(input.size),
            "c".repeat(output.size),
            "c".repeat(depth + 1),
        )

        stream.printf(
            "\\# & \\multicolumn{%d}{c}{\\categoryheader{Input}} & " +
                "\\multicolumn{%d}{c}{\\categoryheader{Output}} & \\coltime \\\\%n",
            input.size,
            output.size,
        )

        val wrapColumnHeader = { hdr: String -> "\\variableheader{$hdr}" }

        stream.printf(
            "  & %s &%s \\\\%n",
            input.map { it.name }
                .map { escape(it) }
                .map(wrapColumnHeader)
                .reduce { a, b -> "$a & $b" },
            output.map { it.name }
                .map { escape(it) }
                .map(wrapColumnHeader)
                .reduce { a, b -> "$a & $b" },
        )

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

    override fun printCell(v: ProgramVariable, row: TableRow) {
        val cell = helper.columns[v.name]?.get(currentRow - 1)!!
        stream.printf(
            " & %15s",
            if (options.noRepetitionLines) {
                cell.content
            } else {
                if (cell.endGroup) {
                    tikzMarkAndDraw(v.name)
                } else if (cell.secondInGroup) {
                    tikzMark(v.name)
                } else if (cell.inBetween) {
                    ""
                } else {
                    cell.content
                }
            },
        )
    }

    override fun printRowDuration(duration: Duration) {
        stream.printf(" & %15s", beautifyDuration(duration))
    }

    override fun printGroupDuration(dur: Duration, rowSpan: Int) {
        stream.printf(" & \\rowgroupduration{%d}{%s}", rowSpan, beautifyDuration(dur))
    }

    override fun cellFormatter(c: TestTableLanguageParser.CellContext): String = c.accept(LatexPrinter(options))

    private fun beautifyDuration(d: Duration): String = when (d) {
        is Duration.Omega -> "\\TIMEOMEGA"
        is Duration.ClosedInterval -> {
            (
                if (d.lower == d.upper) {
                    "{${d.lower}"
                } else {
                    "[${d.lower},${d.upper}]$"
                }
                ) + d.modifier.latex()
        }
        is Duration.OpenInterval ->
            String.format("$\\geq%s$", d.lower) + d.modifier.latex()
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
class LatexPrinter(val options: LatexTablePrinterOptions) : TestTableLanguageParserBaseVisitor<String>() {
    private fun latex(command: String, args: Iterable<String>): String =
        "\\$command" + args.map { "{$it}" }.joinToString("")

    private fun latex(command: String, vararg args: ParserRuleContext): String = if (args.isEmpty()) {
        "\\$command"
    } else {
        latex(command, args.map { it.accept(this) })
    }

    override fun visitCell(ctx: TestTableLanguageParser.CellContext): String = accept(ctx.chunk()).reduce { t, u ->
        "$t, $u"
    }.orElse("")

    private fun accept(ctx: Collection<ParserRuleContext>): Stream<String> = ctx.stream().map { c -> c.accept(this) }

    private fun oneOf(vararg ctx: ParserRuleContext?): String {
        val x = ctx.find { Objects.nonNull(it) }
        return if (x != null) x.accept(this) else ""
    }

    override fun visitDontcare(ctx: TestTableLanguageParser.DontcareContext): String = latex("DONTCARE")

    override fun visitI(ctx: TestTableLanguageParser.IContext): String = ctx.text

    override fun visitConstantInt(ctx: TestTableLanguageParser.ConstantIntContext): String = oneOf(ctx.i())

    override fun visitConstantTrue(ctx: TestTableLanguageParser.ConstantTrueContext): String = latex("TRUE")

    override fun visitConstantFalse(ctx: TestTableLanguageParser.ConstantFalseContext): String = latex("FALSE")

    override fun visitSinglesided(ctx: TestTableLanguageParser.SinglesidedContext): String =
        ctx.relational_operator().accept(this) + " " + ctx.expr().accept(this)

    override fun visitInterval(ctx: TestTableLanguageParser.IntervalContext): String =
        "[" + ctx.lower.accept(this) + ", " + ctx.upper.accept(this) + "]"

    override fun visitRelational_operator(ctx: TestTableLanguageParser.Relational_operatorContext): String {
        when (ctx.text) {
            "<=" -> return "\\leq"
            ">=" -> return "\\geq"
            "!=" -> return "\\neg="
            else -> return ctx.text
        }
    }

    override fun visitMinus(ctx: TestTableLanguageParser.MinusContext): String = "-" + ctx.sub.accept(this)

    override fun visitNegation(ctx: TestTableLanguageParser.NegationContext): String = latex("NEGATION", ctx.sub)

    override fun visitParens(ctx: TestTableLanguageParser.ParensContext): String = latex("PARENS", ctx.sub)

    override fun visitCompare(ctx: TestTableLanguageParser.CompareContext): String {
        val a = TestTableLanguageLexer.VOCABULARY.getSymbolicName(ctx.op.type)
        return latex("COMPARE_$a", ctx.left, ctx.right)
    }

    override fun visitMod(ctx: TestTableLanguageParser.ModContext): String = latex("MOD", ctx.left, ctx.right)

    override fun visitMult(ctx: TestTableLanguageParser.MultContext): String = latex("MULT", ctx.left, ctx.right)

    override fun visitFunctioncall(ctx: TestTableLanguageParser.FunctioncallContext): String =
        latex("FUNCTION", ctx.n.text, ctx.expr())

    private fun latex(command: String, n: String, stream: Collection<ParserRuleContext>): String {
        val list = stream.map { a -> a.accept(this) }.toMutableList()
        list.add(0, n)
        return latex(command, list)
    }

    override fun visitLogicalAnd(ctx: TestTableLanguageParser.LogicalAndContext): String =
        latex("LAND", ctx.left, ctx.right)

    override fun visitPlus(ctx: TestTableLanguageParser.PlusContext): String = latex("PLUS", ctx.left, ctx.right)

    override fun visitDiv(ctx: TestTableLanguageParser.DivContext): String = latex("DIV", ctx.left, ctx.right)

    override fun visitInequality(ctx: TestTableLanguageParser.InequalityContext): String =
        latex("NOTEQUAL", ctx.left, ctx.right)

    override fun visitLogicalXor(ctx: TestTableLanguageParser.LogicalXorContext): String =
        latex("XOR", ctx.left, ctx.right)

    override fun visitLogicalOr(ctx: TestTableLanguageParser.LogicalOrContext): String =
        latex("LOR", ctx.left, ctx.right)

    override fun visitEquality(ctx: TestTableLanguageParser.EqualityContext): String =
        latex("EQUAL", ctx.left, ctx.right)

    override fun visitSubstract(ctx: TestTableLanguageParser.SubstractContext): String =
        latex("SUB", ctx.left, ctx.right)

    override fun visitVariable(ctx: TestTableLanguageParser.VariableContext): String =
        escape(ctx.IDENTIFIER().symbol.text) + if (ctx.RBRACKET() != null) "[" + ctx.i().accept(this) + "]" else ""

    override fun visitGuardedcommand(ctx: TestTableLanguageParser.GuardedcommandContext): String =
        throw TODO("guarded command to latex is not implemented")
}