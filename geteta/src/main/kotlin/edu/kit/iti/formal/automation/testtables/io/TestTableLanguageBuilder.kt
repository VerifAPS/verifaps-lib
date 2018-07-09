package edu.kit.iti.formal.automation.testtables.io

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.*

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
        val fd = FunctionDeclaration(ctx.name.text)
        fd.returnType.identifier = ctx.rt.text
        fd.stBody = IEC61131Facade.statements(ctx.STCODE().text)
        ctx.vardt().forEach {
            fd.scope.add(VariableDeclaration(it.arg.text, VariableDeclaration.INPUT,
                    scope.resolveDataType(it.dt.text)))
        }
        current.functions += fd
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
        ctx.kc().forEach {
            val name = it.key.text
            val column = gtt.getSMVVariable(it.key.text)
            val cell = IOFacade.parseCellExpression(it.cell(), column, gtt);
            s.add(gtt.ioVariables[name]!!, cell)
        }
        return s
    }
}

class TimeParser : TestTableLanguageBaseVisitor<Duration>() {
    override fun visitTimeSingleSided(ctx: TestTableLanguageParser.TimeSingleSidedContext): Duration {
        val d = Duration()
        d.lower = ctx.INTEGER().text.toInt()
        if (ctx.op.text == ">")
            d.lower += 1
        d.upper = -1
        if (ctx.pflag != null) d.pflag = true
        assert(d.invariant())
        return d
    }

    override fun visitTimeInterval(ctx: TestTableLanguageParser.TimeIntervalContext): Duration {
        val p = ctx.fixed_interval()
        val d = Duration()
        if (p.c != null) {
            val i = Integer.parseInt(p.c.text)
            d.lower = i
            d.upper = i
        } else if (p.dc != null) {
            d.lower = 0
            d.upper = -1
        } else {
            d.lower = Integer.parseInt(p.a.text)
            if (p.inf != null)
                d.upper = -1
            else
                d.upper = Integer.parseInt(p.b.text)
        }
        if (ctx.pflag != null) d.pflag = true
        assert(d.invariant())
        return d
    }

    override fun visitTimeDontCare(ctx: TestTableLanguageParser.TimeDontCareContext?): Duration = Duration()

    override fun visitTimeOmega(ctx: TestTableLanguageParser.TimeOmegaContext) = Duration.OMEGA
}
