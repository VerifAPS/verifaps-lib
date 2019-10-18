package edu.kit.iti.formal.automation.testtables.io

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
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
class TestTableLanguageBuilder() : TestTableLanguageBaseVisitor<Unit>() {
    val testTables = arrayListOf<GeneralizedTestTable>()
    private lateinit var current: GeneralizedTestTable
    private val scope = Scope.defaultScope()

    init {
        scope.types.register("ENUM", EnumerateType("ENUM", arrayListOf("a"), "a"))
        scope.types.register("BOOLEAN", AnyBit.BOOL)
    }

    override fun visitTable(ctx: TestTableLanguageParser.TableContext) {
        current = GeneralizedTestTable()
        testTables += current
        current.name = ctx.IDENTIFIER().text
        visitChildren(ctx)

        current.options.relational = ctx.r != null
    }

    override fun visitGroup(ctx: TestTableLanguageParser.GroupContext) {
        current.region = ctx.accept(RegionVisitor(current)) as Region
    }

    override fun visitOpts(ctx: TestTableLanguageParser.OptsContext) {
        ctx.kv().forEach {
            current.addOption(it.key.text, it.variable()?.text ?: it.constant()?.text ?: "")
        }
    }

    data class VariableModifier(
            val category: ColumnCategory,
            val next: Boolean,
            val state: Boolean
    )

    fun visit(ctx: TestTableLanguageParser.Var_modifierContext): VariableModifier {
        val assert = ctx.ASSERT() != null
        val assume = ctx.ASSUM() != null
        val next = ctx.NEXT() != null
        val input = ctx.INPUT() != null
        val output = ctx.OUTPUT() != null
        val type = when {
            (assert || input) && !(output || assert) -> ColumnCategory.ASSUME
            !(assume || input) && (output || assert) -> ColumnCategory.ASSERT
            else -> throw RuntimeException("Modifier clash in line ${ctx.start.line}.")
        }
        return VariableModifier(type, output || next, ctx.STATE() != null)
    }

    override fun visitColumn(ctx: TestTableLanguageParser.ColumnContext) {
        val modifier = visit(ctx.var_modifier())
        require(!modifier.next) {
            "Next modifier You provided a wrong set of modifier '$modifier' for column in line ${ctx.start.line}."
        }

        val name = ctx.name.text
        val dt = scope.resolveDataType(ctx.dt.text)
        val exprs = ctx.expr()
        val lt = DefaultTypeTranslator.INSTANCE.translate(dt)
        val type = modifier.category
        val c = ProjectionVariable(name, dt, lt, type, exprs)
        current.add(c)
    }

    override fun visitSignature(ctx: TestTableLanguageParser.SignatureContext) {
        val dt = scope.resolveDataType(ctx.dt.text)
        val modifier = visit(ctx.var_modifier())
        val type = modifier.category
        val lt = DefaultTypeTranslator.INSTANCE.translate(dt)

        ctx.variableDefinition().forEach {
            when (it) {
                is TestTableLanguageParser.VariableAliasDefinitionSimpleContext -> {
                    val newName: String? = it.newName?.text
                    val realName = it.n.text
                    val v = ProgramVariable(realName, dt, lt, type)
                    if (newName != null) {
                        v.realName = v.name
                        v.name = newName
                    }
                    current.add(v)
                }
                is TestTableLanguageParser.VariableAliasDefinitionRelationalContext -> {
                    val newName: String? = it.newName?.text
                    val realName = it.n.text
                    val programRun = it.INTEGER().text.toInt()
                    val v = ProgramVariable(realName, dt, lt, type,
                            modifier.state, modifier.next, programRun)
                    if (newName != null) {
                        v.realName = v.name
                        v.name = newName
                    }
                    current.add(v)
                }
                is TestTableLanguageParser.VariableRunsDefinitionContext -> {
                    val realName = it.n.text
                    it.INTEGER().map { it.text.toInt() }.forEach { i ->
                        val v = ProgramVariable(realName, dt, lt, type, modifier.state, modifier.next, i)
                        current.add(v)
                    }
                }
            }
        }
    }

    override fun visitFreeVariable(ctx: TestTableLanguageParser.FreeVariableContext) {
        val dt = scope.resolveDataType(ctx.dt.text)
        val lt = DefaultTypeTranslator.INSTANCE.translate(dt)
        val fv = ConstraintVariable(ctx.name.text, dt, lt)
        ctx.cell().let {
            fv.constraint = it
        }
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
        val id = ctx.id?.text ?: "g" + (ctx.idi?.text?.toInt() ?: ++currentId)
        val r = Region(id)
        if (ctx.time() != null)
            r.duration = ctx.time().accept(TimeParser())

        ctx.children.forEach {
            val tn = it.accept(this)
            if (tn != null) r.children.add(tn)
        }
        return r
    }


    override fun visitRow(ctx: TestTableLanguageParser.RowContext): TableRow {
        val id = ctx.id?.text ?: String.format("r%02d", ctx.idi?.text?.toInt() ?: ++currentId)
        val s = TableRow(id)
        s.duration = ctx.time()?.accept(TimeParser()) ?: Duration.ClosedInterval(1, 1)
        ctx.kc().forEach {
            val name = it.IDENTIFIER().text
            val run = it.INTEGER()?.text?.toInt()
            //val column = gtt.getSMVVariable(it.key.text)
            //val cell = IOFacade.exprToSMV(it.cell(), column, gtt);
            s.rawFields[gtt.getProgramVariables(name, run)] = it.cell()
        }

        if (ctx.pause() != null) {
            s.pauseProgramRuns = ctx.pause().INTEGER().map { it.text.toInt() }.toMutableList()
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
