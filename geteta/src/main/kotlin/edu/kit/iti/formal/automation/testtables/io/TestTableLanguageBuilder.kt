package edu.kit.iti.formal.automation.testtables.io

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.*
import org.antlr.v4.runtime.CharStreams

/**
 *
 * @author Alexander Weigl
 * @version 1 (06.07.18)
 */
class TestTableLanguageBuilder : TestTableLanguageBaseVisitor<Unit>() {
    val testTables = arrayListOf<GeneralizedTestTable>()
    private lateinit var current: GeneralizedTestTable
    private val scope = Scope.defaultScope()

    override fun visitTable(ctx: TestTableLanguageParser.TableContext) {
        current = GeneralizedTestTable()
        testTables += current
        current.name = ctx.IDENTIFIER().text
        visitChildren(ctx)
    }

    override fun visitGroup(ctx: TestTableLanguageParser.GroupContext) {
        current.region = ctx.accept(RegionVisitor(current)) as Region
    }

    override fun visitOpts(ctx: TestTableLanguageParser.OptsContext) {
        ctx.kv().forEach {
            current.addOption(it.key.text, it.variable()?.text ?: it.constant()?.text ?: "")
        }
    }

    override fun visitSignature(ctx: TestTableLanguageParser.SignatureContext) {
        val isState = ctx.state != null
        val newName: String? = ctx.newName?.text
        val v = IoVariable(ctx.name.text, scope.resolveDataType(ctx.dt.text),
                if (isState) {
                    if (ctx.io.text == "input") IoVariableType.STATE_INPUT
                    else IoVariableType.STATE_OUTPUT
                } else {
                    if (ctx.io.text == "input") IoVariableType.INPUT
                    else IoVariableType.OUTPUT
                })
        if (newName != null) {
            v.realName = v.name
            v.name = newName
        }
        current.add(v)
    }

    override fun visitFreeVariable(ctx: TestTableLanguageParser.FreeVariableContext) {
        val fv = ConstraintVariable(ctx.name.text, scope.resolveDataType(ctx.dt.text)

        )
        current.add(fv)
    }

    override fun visitFunction(ctx: TestTableLanguageParser.FunctionContext) {
        val code = ctx.FUNCTION().text
        val pou = IEC61131Facade.file(CharStreams.fromString(code))
        current.functions += pou[0] as FunctionDeclaration
    }
}

class RegionVisitor(private val gtt: GeneralizedTestTable) : TestTableLanguageBaseVisitor<TableNode>() {
    var currentId = 0

    override fun visitGroup(ctx: TestTableLanguageParser.GroupContext): Region {
        val id = ctx.id?.text?.toInt() ?: ++currentId;
        val r = Region(id)
        if (ctx.time() != null)
            r.duration = ctx.time().accept(TimeParser())

        ctx.children.forEach {
            val tn = it.accept(this)
            if (tn != null) r.children.add(tn)
        }
        return r
    }


    override fun visitRow(ctx: TestTableLanguageParser.RowContext): State {
        val id = ctx.id?.text?.toInt() ?: ++currentId;
        val s = State(id)
        s.duration = ctx.time().accept(TimeParser())
        ctx.kc().forEach {
            val name = it.key.text
            //val column = gtt.getSMVVariable(it.key.text)
            //val cell = IOFacade.exprToSMV(it.cell(), column, gtt);
            s.rawFields[gtt.ioVariables[name]!!] = it.cell()
        }
        return s
    }
}

class TimeParser : TestTableLanguageBaseVisitor<Duration>() {
    override fun visitTimeSingleSided(ctx: TestTableLanguageParser.TimeSingleSidedContext): Duration {
        val lower =
                ctx.INTEGER().text.toInt() +
                        if (ctx.op.text == ">") 1 else 0
        return Duration.OpenInterval(
                lower, ctx.pflag != null
        )
    }

    override fun visitTimeClosedInterval(ctx: TestTableLanguageParser.TimeClosedIntervalContext): Duration {
        return Duration.ClosedInterval(
                ctx.l.text.toInt(),
                ctx.u.text.toInt(),
                ctx.pflag != null)
    }

    override fun visitTimeOpenInterval(ctx: TestTableLanguageParser.TimeOpenIntervalContext): Duration {
        return Duration.OpenInterval(ctx.l.text.toInt(), ctx.pflag != null)
    }

    override fun visitTimeFixed(ctx: TestTableLanguageParser.TimeFixedContext): Duration {
        val i = ctx.INTEGER().text.toInt()
        return Duration.ClosedInterval(i, i, false)
    }

    override fun visitTimeDontCare(ctx: TestTableLanguageParser.TimeDontCareContext?): Duration = Duration.OpenInterval(0, false)

    override fun visitTimeOmega(ctx: TestTableLanguageParser.TimeOmegaContext) = Duration.Omega
}
