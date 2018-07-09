package edu.kit.iti.formal.automation.testtables.algorithms

import com.google.common.collect.Streams
import edu.kit.iti.formal.automation.testtables.PrintTable
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import org.antlr.v4.runtime.ParserRuleContext
import org.apache.commons.lang3.NotImplementedException
import java.util.*
import java.util.stream.Stream

/**
 * @author Alexander Weigl
 * @version 1 (01.03.18)
 */
class LatexPrinter : TestTableLanguageBaseVisitor<String>() {
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
    fun latex(command: String, args: Stream<String>): String {
        return "\\$command" +
                args.map { a -> "{$a}" }
                        .reduce { t, u -> "$t$u" }
    }

    fun latex(command: String, vararg args: ParserRuleContext): String {
        return if (args.isEmpty()) {
            "\\$command"
        } else {
            latex(command, Arrays.stream(args).map { a -> a.accept(this) })
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
        return latex("FUNCTION", ctx.n.text, ctx.expr().stream())
    }

    private fun latex(command: String, n: String, stream: Stream<out ParserRuleContext>): String {
        return latex(command,
                Streams.concat(setOf(n).stream(),
                        stream.map { a -> a.accept(this) }
                )
        )
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
        return PrintTable.escape(ctx.IDENTIFIER().symbol.text) + if (ctx.RBRACKET() != null) "[" + ctx.i().accept(this) + "]" else ""
    }

    override fun visitGuardedcommand(ctx: TestTableLanguageParser.GuardedcommandContext): String {
        throw NotImplementedException("guarded command to latex is not implemented")
    }
}
