package edu.kit.iti.formal.automation.testtables.print

import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.Duration
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.ProgramVariable
import edu.kit.iti.formal.util.CodeWriter

/**
 *
 * @author Alexander Weigl
 * @version 1 (08.08.18)
 */
class HtmlTablePrinterOptions {
    var progressFlag = "<sup>p</sup>"
    var dontCare = "&dash;"
    var mathPlus = "&plus;"
    var mathMult = "&times;"
    var mathMinus = "&minus;"
    var mathEquals = "&equals;"
    var mathNot = "&not;"
    var mathLessThan = "&lt;"
    var mathGreaterThan = "&gt;"
    var mathLessEquals = "&le;"
    var mathGreaterEquals = "&ge;"
    var omegaRepetition = "&infin;"
    var mathAnd = "&and;"
    var mathOr = "&or;"
    val mathDiv = "&div;"
    val mathXor = "&mod;"
    val mathUnequal = "&ne;"

}

class HTMLTablePrinter(gtt: GeneralizedTestTable, stream: CodeWriter,
                       val options: HtmlTablePrinterOptions = HtmlTablePrinterOptions()
) : AbstractTablePrinter(gtt, stream) {
    override fun contentBegin() {
    }

    override fun tableBegin() {
        val inputVars =
                input.joinToString {
                    """<th class="varheader input">${it.name}</th>\n"""
                }

        val outputVars =
                output.joinToString {
                    """<th class="varheader output">${it.name}</th>\n"""
                }

        stream.println("""
            <table class='gtt'>
                <thead>
                    <tr class="categories">
                        <th>#</th>
                        <th classes="input" colSpan="${input.size}">input</th>
                        <th classes="output" colSpan="${output.size}">output</th>
                        <th classes="cycle" colSpan="${depth + 1}">cycle</th>
                    </tr>
                    <tr class="variables">
                        <th></th>
                        $inputVars
                        $outputVars
                    </tr>
                </thead>
                <tbody>
            """
        )
    }

    override fun tableEnd() {
        stream.println("</tbody>\n</table>")
    }

    override fun contentEnd() {}

    override fun regionBegin() {}
    override fun regionEnd() {}


    override fun rowBegin() {
        stream.print("<tr><td class=\"row-number\">$currentRow</td>")
    }

    override fun rowEnd() {
        stream.println("</tr>")
    }

    override fun printGroupDuration(dur: Duration, rowSpan: Int) {
        stream.print("""<td rowSpan="$rowSpan" class="group-duration">${beautifyDuration(dur)}</td>

        """)
    }

    override fun printCell(v: ProgramVariable) {
        val cell = helper.columns[v.name]?.get(currentRow - 1)!!
        val content = cell.content
        val c =
                if (cell.inBetween) "in-between"
                else ""
        stream.print("""<td class="cell ${v.name} ${v.dataType} ${v.logicType} ${v.io} $c">$content</td>
        """)
    }

    override fun printRowDuration(duration: Duration) {
        stream.print("""<td class="duration">${beautifyDuration(duration)}</td>
        """)
    }

    override fun cellFormatter(c: TestTableLanguageParser.CellContext): String {
        return c.accept(HtmlExprPrinter(options))
    }

    override fun printPreamble() {
        stream.println("""
            <html>
                <head>
                    <attributes>
                    </attributes>
                    <link rel="stylesheet" href="gtt-attributes.css"/>
                </head>
                <body>
        """.trimIndent())

    }

    override fun printPostamble() {
        stream.write("</body></html>")
    }

    private fun beautifyDuration(d: Duration): String =
            when (d) {
                is Duration.Omega -> options.omegaRepetition
                is Duration.ClosedInterval -> {
                    (if (d.lower == d.upper) "${d.lower}"
                    else "[${d.lower},${d.upper}]") + (if (d.pflag) options.progressFlag else "")
                }
                is Duration.OpenInterval ->
                    String.format("${options.mathGreaterEquals}%s", d.lower) + (if (d.pflag) options.progressFlag else "")
            }
}

class HtmlExprPrinter(val options: HtmlTablePrinterOptions) : TestTableLanguageBaseVisitor<String>() {
    override fun visitCell(ctx: TestTableLanguageParser.CellContext) = ctx.chunk().joinToString(",") { it.accept(this) }

    override fun visitDontcare(ctx: TestTableLanguageParser.DontcareContext?): String = options.dontCare
    override fun visitI(ctx: TestTableLanguageParser.IContext) = span("integer", ctx.text)
    override fun visitConstantInt(ctx: TestTableLanguageParser.ConstantIntContext) = span("integer", ctx.text)

    override fun visitConstantTrue(ctx: TestTableLanguageParser.ConstantTrueContext?) = span("boolean", "true")


    override fun visitConstantFalse(ctx: TestTableLanguageParser.ConstantFalseContext?) = span("boolean", "false")

    override fun visitSinglesided(ctx: TestTableLanguageParser.SinglesidedContext): String {
        return span("constraint",
                ctx.op.accept(this) + ctx.expr().accept(this))
    }

    override fun visitInterval(ctx: TestTableLanguageParser.IntervalContext) = span("interval", "[${ctx.lower.accept(this)}, ${ctx.upper.accept(this)}]")

    override fun visitRelational_operator(ctx: TestTableLanguageParser.Relational_operatorContext) = when {
        ctx.EQUALS() != null -> options.mathEquals
        ctx.GREATER_EQUALS() != null -> options.mathGreaterEquals
        ctx.LESS_THAN() != null -> options.mathLessThan
        ctx.GREATER_THAN() != null -> options.mathGreaterThan
        ctx.LESS_EQUALS() != null -> options.mathLessEquals
        else -> "n/a"
    }

    override fun visitMinus(ctx: TestTableLanguageParser.MinusContext) =
            span("minus", "-" + ctx.sub.accept(this))

    override fun visitNegation(ctx: TestTableLanguageParser.NegationContext) = span("negate", "${options.mathNot} " + ctx.sub.accept(this))

    override fun visitParens(ctx: TestTableLanguageParser.ParensContext) = "(${ctx.expr().accept(this)})"

    override fun visitCompare(ctx: TestTableLanguageParser.CompareContext) = ctx.left.accept(this) + ctx.op.text + ctx.right.accept(this)

    override fun visitMod(ctx: TestTableLanguageParser.ModContext) = ctx.left.accept(this) + " mod " + ctx.right.accept(this)


    override fun visitMult(ctx: TestTableLanguageParser.MultContext) = ctx.left.accept(this) + " ${options.mathMult} " + ctx.right.accept(this)

    override fun visitBinguardedCommand(ctx: TestTableLanguageParser.BinguardedCommandContext) = ctx.guardedcommand().accept(this)

    override fun visitFunctioncall(ctx: TestTableLanguageParser.FunctioncallContext): String =
            ctx.n.text + "(" + ctx.expr().joinToString(", ") { it.accept(this) } + ")"

    override fun visitBvariable(ctx: TestTableLanguageParser.BvariableContext) = ctx.variable().accept(this)

    override fun visitLogicalAnd(ctx: TestTableLanguageParser.LogicalAndContext) = ctx.left.accept(this) + " ${options.mathAnd} " + ctx.right.accept(this)

    override fun visitPlus(ctx: TestTableLanguageParser.PlusContext) = ctx.left.accept(this) + " ${options.mathPlus} " + ctx.right.accept(this)

    override fun visitDiv(ctx: TestTableLanguageParser.DivContext) = ctx.left.accept(this) + " ${options.mathDiv} " + ctx.right.accept(this)

    override fun visitInequality(ctx: TestTableLanguageParser.InequalityContext) = ctx.left.accept(this) + " ${options.mathUnequal}" + ctx.right.accept(this)

    override fun visitLogicalXor(ctx: TestTableLanguageParser.LogicalXorContext) = ctx.left.accept(this) + " ${options.mathXor} " + ctx.right.accept(this)

    override fun visitBconstant(ctx: TestTableLanguageParser.BconstantContext) = ctx.constant().accept(this)

    override fun visitLogicalOr(ctx: TestTableLanguageParser.LogicalOrContext) = ctx.left.accept(this) + " ${options.mathOr} " + ctx.right.accept(this)

    override fun visitEquality(ctx: TestTableLanguageParser.EqualityContext) = ctx.left.accept(this) + " ${options.mathEquals} " + ctx.right.accept(this)


    override fun visitSubstract(ctx: TestTableLanguageParser.SubstractContext) = ctx.left.accept(this) + " ${options.mathMinus} " + ctx.right.accept(this)


    override fun visitVariable(ctx: TestTableLanguageParser.VariableContext) = span("variable", ctx.text)

    override fun visitGuardedcommand(ctx: TestTableLanguageParser.GuardedcommandContext): String {
        val body = ctx.GUARD().zip(ctx.expr())
                .joinToString("\n") { (a, b) ->
                    a.accept(this) + "::" + b.accept(this)
                }
        return """if\ n${body}\nfi"""
    }
}

private fun span(cl: String, v: String) = """<span class = "$cl">$v</span>"""
