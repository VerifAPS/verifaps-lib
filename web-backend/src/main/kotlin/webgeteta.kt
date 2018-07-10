package edu.kit.iti.formal.automation.web

import edu.kit.iti.formal.automation.st.ast.PouElements
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.automation.visitors.Utils
import io.ktor.application.call
import io.ktor.http.ContentType
import io.ktor.http.HttpStatusCode
import io.ktor.request.receive
import io.ktor.response.respondText
import io.ktor.routing.Route
import io.ktor.routing.post
import kotlinx.html.*
import kotlinx.html.stream.appendHTML
import org.antlr.v4.runtime.CharStreams
import java.io.PrintWriter
import java.io.StringWriter
import java.util.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (06.07.18)
 */
fun Route.geteta() {
    post("/geteta/generate") {
        val code = context.receive<PouElements>()
        val program = Utils.findProgram(code)
        if (program != null) {
            context.respondText(ContentType.Text.Plain) {
                GetetaFacade.generateInterface(scope = program.scope)
            }
            return@post
        }

        context.respondText(ContentType.Text.Plain, HttpStatusCode.InternalServerError) {
            "No program was given. Could not extract interface."
        }
    }

    post("/geteta/render") {
        val table = call.receive<String>()
        val gtt = GetetaFacade.parseTable(CharStreams.fromString(table))
        call.respondText(ContentType.Text.Html) {
            val backend = StringWriter()
            val stream = PrintWriter(backend)
            try {
                HTMLTablePrinter(gtt, stream).print()
            } catch (e: Exception) {
                e.printStackTrace(stream)
            }
            backend.toString()
        }
    }

    post("/geteta/proof") {

    }
}


class HTMLTablePrinter(val gtt: GeneralizedTestTable, var stream: PrintWriter) {
    val DONT_CARE = "&mid;"
    private var currentRow = 0

    val input = gtt.ioVariables.filter { it.isInput }
    val output = gtt.ioVariables.filter { it.isOutput }
    val durations = Stack<Pair<Duration, Int>>()
    val specialChars = hashMapOf("<" to "&lt;", ">" to "&gt;")
    //val totalNumSteps = gtt.region.count()
    val columns = LinkedHashMap<String, ArrayList<String>>()
    val depth = gtt.region.depth()

    public fun print() {
        fillColumns()
        stream.appendHTML().table {
            thead {
                tr(classes = "categories") {
                    th { "#" }
                    th(classes = "input") {
                        colSpan = input.size.toString()
                        +("input")
                    }
                    th(classes = "output") {
                        colSpan = output.size.toString()
                        +("output")

                    }
                    th(classes = "time") {
                        colSpan = (depth + 1).toString()
                        +("time")
                    }
                }
                tr(classes = "variables") {
                    th {}
                    input.forEach {
                        th(classes = "varheader input") { +it.name }
                    }

                    output.forEach {
                        th(classes = "varheader output") { +it.name }
                    }

                }
            }
            tbody {
                gtt.region.children.forEach { printTableNode(it, this) }
            }
        }
    }

    private fun fillColumns() {
        gtt.ioVariables.forEach { columns[it.name] = ArrayList() }
        gtt.generateSmvExpression()

        //prefill
        val flat = gtt.region.flat()
        flat.forEach {
            it.rawFields.forEach { k, v ->
                columns[k.name]!!.add(parseAndSafePrint(v))
            }
        }
    }

    private fun parseAndSafePrint(ctx: TestTableLanguageParser.CellContext?) = ctx?.accept(HtmlExprPrinter) ?: ""

    private fun printTableNode(b: TableNode, tbody: TBODY) {
        when (b) {
            is Region -> {
                val push = b.duration to b.count()
                durations.add(push)
                b.children.forEach { printTableNode(it, tbody) }
            }
            is State -> {
                tbody.tr {
                    td(classes = "row-number") { text(currentRow) }
                    input.forEach { td(classes = "input") { unsafe { +(columns[it.name]?.get(currentRow) ?: "") } } }
                    output.forEach { td(classes = "output") { unsafe { +(columns[it.name]?.get(currentRow) ?: "") } } }

                    td(classes = "time") { unsafe { +beautifyDuration(b.duration) } }

                    while (!durations.empty()) {
                        val (dur, d) = durations.pop()
                        td(classes = "group-time") { unsafe { +beautifyDuration(dur) } }
                    }
                }
                currentRow += 1
            }
        }
    }

    private val P_FLAG = "<sup>p</sup>"

    private fun beautifyDuration(d: Duration): String =
            when (d) {
                is Duration.Omega -> HtmlExprPrinter.OMEGA
                is Duration.ClosedInterval -> {
                    (if (d.lower == d.upper) "${d.lower}"
                    else "[${d.lower},${d.upper}]") + (if (d.pflag) P_FLAG else "")
                }
                is Duration.OpenInterval ->
                    String.format("${HtmlExprPrinter.MATH_GE}%s", d.lower) + (if (d.pflag) P_FLAG else "")
            }
}

object HtmlExprPrinter : TestTableLanguageBaseVisitor<String>() {

    val MATH_PLUS = "&plus;"
    val MATH_MULT = "&times;"
    val MATH_MINUS = "&minus;"
    val MATH_EQUALS = "&equals;"
    val MATH_NOT = "&not;"
    val MATH_LT = "&lt;"
    val MATH_GT = "&gt;"
    val MATH_LE = "&le;"
    val MATH_GE = "&ge;"
    val OMEGA = "&infin;"
    val DONTCARE = "&mid;"
    val MATH_AND = "&and;"
    val MATH_OR = "&or;"

    override fun visitCell(ctx: TestTableLanguageParser.CellContext) = ctx.chunk().joinToString(",") { it.accept(this) }
    override fun visitChunk(ctx: TestTableLanguageParser.ChunkContext) = visitChildren(ctx)

    override fun visitDontcare(ctx: TestTableLanguageParser.DontcareContext?): String = DONTCARE
    override fun visitI(ctx: TestTableLanguageParser.IContext) = span("integer", ctx.text)
    override fun visitConstantInt(ctx: TestTableLanguageParser.ConstantIntContext) = span("integer", ctx.text)

    override fun visitConstantTrue(ctx: TestTableLanguageParser.ConstantTrueContext?) = span("boolean", "true")

    private fun span(cl: String, v: String) = """<span class="$cl">$v</span>"""

    override fun visitConstantFalse(ctx: TestTableLanguageParser.ConstantFalseContext?) = span("boolean", "false")

    override fun visitSinglesided(ctx: TestTableLanguageParser.SinglesidedContext): String {
        return span("constraint",
                ctx.op.accept(this) + ctx.expr().accept(this));
    }

    override fun visitInterval(ctx: TestTableLanguageParser.IntervalContext) = span("interval", "[${ctx.lower.accept(this)}, ${ctx.upper.accept(this)}]")

    override fun visitRelational_operator(ctx: TestTableLanguageParser.Relational_operatorContext) = when {
        ctx.EQUALS() != null -> MATH_EQUALS
        ctx.GREATER_EQUALS() != null -> MATH_GE
        ctx.LESS_THAN() != null -> MATH_LT
        ctx.GREATER_THAN() != null -> MATH_GT
        ctx.LESS_EQUALS() != null -> MATH_LE
        else -> "n/a"
    }

    override fun visitMinus(ctx: TestTableLanguageParser.MinusContext) =
            span("minus", "-" + ctx.sub.accept(this))

    override fun visitNegation(ctx: TestTableLanguageParser.NegationContext) = span("negate", "$MATH_NOT " + ctx.sub.accept(this))

    override fun visitParens(ctx: TestTableLanguageParser.ParensContext) = "(${ctx.expr().accept(this)})"

    override fun visitCompare(ctx: TestTableLanguageParser.CompareContext) = ctx.left.accept(this) + ctx.op.text + ctx.right.accept(this)

    override fun visitMod(ctx: TestTableLanguageParser.ModContext) = ctx.left.accept(this) + " mod " + ctx.right.accept(this)


    override fun visitMult(ctx: TestTableLanguageParser.MultContext) = ctx.left.accept(this) + " $MATH_MULT " + ctx.right.accept(this)

    override fun visitBinguardedCommand(ctx: TestTableLanguageParser.BinguardedCommandContext) = ctx.guardedcommand().accept(this)

    val MATH_DIV = "&div;"
    val MATH_XOR = "&mod;"
    val MATH_UNEQUAL = "&ne;"

    override fun visitFunctioncall(ctx: TestTableLanguageParser.FunctioncallContext): String =
            ctx.n.text + "(" + ctx.expr().joinToString(", ") { it.accept(this) } + ")"

    override fun visitBvariable(ctx: TestTableLanguageParser.BvariableContext) = ctx.variable().accept(this)

    override fun visitLogicalAnd(ctx: TestTableLanguageParser.LogicalAndContext) = ctx.left.accept(this) + " $MATH_AND " + ctx.right.accept(this)

    override fun visitPlus(ctx: TestTableLanguageParser.PlusContext) = ctx.left.accept(this) + " $MATH_PLUS " + ctx.right.accept(this)

    override fun visitDiv(ctx: TestTableLanguageParser.DivContext) = ctx.left.accept(this) + " $MATH_DIV " + ctx.right.accept(this)

    override fun visitInequality(ctx: TestTableLanguageParser.InequalityContext) = ctx.left.accept(this) + " $MATH_UNEQUAL " + ctx.right.accept(this)

    override fun visitLogicalXor(ctx: TestTableLanguageParser.LogicalXorContext) = ctx.left.accept(this) + " $MATH_XOR " + ctx.right.accept(this)

    override fun visitBconstant(ctx: TestTableLanguageParser.BconstantContext) = ctx.constant().accept(this)

    override fun visitLogicalOr(ctx: TestTableLanguageParser.LogicalOrContext) = ctx.left.accept(this) + " $MATH_OR " + ctx.right.accept(this)

    override fun visitEquality(ctx: TestTableLanguageParser.EqualityContext) = ctx.left.accept(this) + " $MATH_EQUALS " + ctx.right.accept(this)


    override fun visitSubstract(ctx: TestTableLanguageParser.SubstractContext) = ctx.left.accept(this) + " $MATH_MINUS " + ctx.right.accept(this)


    override fun visitVariable(ctx: TestTableLanguageParser.VariableContext) = span("variable", ctx.text)

    override fun visitGuardedcommand(ctx: TestTableLanguageParser.GuardedcommandContext): String {
        val body = ctx.GUARD().zip(ctx.expr())
                .joinToString("\n") { (a, b) ->
                    a.accept(this) + "::" + b.accept(this)
                }
        return """if\n${body}\nfi"""
    }
}
