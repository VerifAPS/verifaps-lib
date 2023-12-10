package edu.kit.iti.formal.automation.testtables.io


import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException
import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.st.ast.Position
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParserBaseVisitor
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.util.fail
import edu.kit.iti.formal.util.info
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.tree.TerminalNode

/**
 *
 * @author Alexander Weigl
 * @version 1 (06.07.18)
 */
class TestTableLanguageBuilder(preDefinedTimeConstants: Map<String, Int>) : TestTableLanguageParserBaseVisitor<Unit>() {
    val testTables = arrayListOf<GeneralizedTestTable>()
    private val timeConstants: MutableMap<String, Int> = HashMap(preDefinedTimeConstants)

    private lateinit var current: GeneralizedTestTable
    private val scope = Scope.defaultScope()

    init {
        scope.types.register("ENUM", EnumerateType("ENUM", arrayListOf("a"), "a"))
        scope.types.register("BOOLEAN", AnyBit.BOOL)
    }


    private fun getProgramRun(it: TestTableLanguageParser.IntOrIdContext) = if (it.id != null) {
        val idx = current.programRuns.indexOf(it.id.text)
        if (idx < 0) error("Program run unknown ${it.id.text}")
        else idx
    } else it.i().text.toInt()


    override fun visitTable(ctx: TestTableLanguageParser.TableContext) {
        current = GeneralizedTestTable()
        testTables += current
        visitChildren(ctx)
    }

    override fun visitDecl_time_const(ctx: TestTableLanguageParser.Decl_time_constContext) {
        val name = ctx.id.text
        val defaultValue = ctx.v.text.toInt()
        if (name !in timeConstants) {
            timeConstants[name] = defaultValue
        }
    }

    override fun visitInheritance_signature(ctx: TestTableLanguageParser.Inheritance_signatureContext) {
        val name = ctx.IDENTIFIER().text
        val gtt = testTables.find { it.name == name }
                ?: error("Could not find table ${name} to inherit from.")
        gtt.programVariables.forEach { current.programVariables.add(it.clone()) }
        gtt.constraintVariables.forEach { current.constraintVariables.add(it.copy()) }
    }

    override fun visitTableHeaderFunctional(ctx: TestTableLanguageParser.TableHeaderFunctionalContext) {
        current.name = ctx.name.text
        current.options.relational = false
        current.ensureProgramRuns()
    }

    override fun visitTableHeaderRelational(ctx: TestTableLanguageParser.TableHeaderRelationalContext) {
        current.name = ctx.name.text
        current.options.relational = true
        current.programRuns = ctx.run.map { it.text }
        if (current.programRuns.size <= 1) {
            fail(
                    "The number of program runs are less than 2 for relational table ${current.name}. " +
                            "Either this is not a relational table, or program runs are missing.")
        }
    }

    override fun visitGroup(ctx: TestTableLanguageParser.GroupContext) {
        current.region = ctx.accept(RegionVisitor(current, testTables, timeConstants)) as Region
        val nodeIds = mutableSetOf<String>()
        current.region.visit { node ->
            if (node.id in nodeIds) {
                fail("Duplication of row/group id ${node.id}.")
            }
            nodeIds.add(node.id)
        }
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
        val assert = ctx.ASSERT().isNotEmpty()
        val assume = ctx.ASSUME().isNotEmpty()
        val next = ctx.NEXT().isNotEmpty()
        val input = ctx.INPUT().isNotEmpty()
        val output = ctx.OUTPUT().isNotEmpty()
        val type = when {
            (assume || input) && !(output || assert) -> ColumnCategory.ASSUME
            !(assume || input) && (output || assert) -> ColumnCategory.ASSERT
            else -> throw RuntimeException("Modifier clash in line ${Position.start(ctx.start)}.")
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
        val dt = getDataType(ctx.dt.text)
        val modifier = visit(ctx.var_modifier())
        val type = modifier.category
        val lt = DefaultTypeTranslator.INSTANCE.translate(dt)
        val vd = ctx.variableDefinition()
        val vdm = vd.variableAliasDefinitionMulti()
        val vds = vd.variableAliasDefinitionSimple()
        val vdr = vd.variableAliasDefinitionRelational()
        when {
            null != vdm -> {
                val runs = vdm.run.map { getProgramRun(it) }
                for (r in runs) {
                    for (n in vdm.n) {
                        val realName = n.text
                        val v = ProgramVariable(realName, dt, lt, type, modifier.state, modifier.next, r)
                        current.add(v)
                    }
                }
            }
            vds.isNotEmpty() -> {
                vds.forEach {
                    val newName: String? = it.newName?.text
                    val realName = it.n.text
                    val v = ProgramVariable(realName, dt, lt, type)
                    if (newName != null) {
                        v.realName = v.name
                        v.name = newName
                    }
                    current.add(v)
                }
            }
            vdr != null -> {
                val newName: String? = vdr.newName?.text
                val (programRun, realName) = resolveName(vdr.FQ_VARIABLE(), current)
                val v = ProgramVariable(realName, dt, lt, type,
                        modifier.state, modifier.next, programRun)
                if (newName != null) {
                    v.realName = v.name
                    v.name = newName
                }
                current.add(v)
            }
        }
    }

    private fun getDataType(symbol: String): AnyDt {
        return try {
            scope.resolveDataType(symbol)
        } catch (e: DataTypeNotDefinedException) {
            if (symbol.startsWith("ENUM_")) {
                EnumerateType(symbol.substring("ENUM_".length), arrayListOf(""))
            } else {
                throw e
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

class RegionVisitor(private val gtt: GeneralizedTestTable,
                    private val tables: List<GeneralizedTestTable>,
                    timeConstants: Map<String, Int>) : TestTableLanguageParserBaseVisitor<TableNode>() {
    private var currentId = 0
    private val timeParser = TimeParser(timeConstants)

    private fun getProgramRun(it: TestTableLanguageParser.IntOrIdContext) = if (it.id != null) {
        val idx = gtt.programRuns.indexOf(it.id.text)
        if (idx < 0) error("Program run unknown ${it.id.text}")
        else idx
    } else it.i().text.toInt()


    override fun visitGroup(ctx: TestTableLanguageParser.GroupContext): Region {
        if (ctx.goto_().isNotEmpty()) {
            info("Handling of goto commands in regions currently not supported")
        }
        val id = ctx.id?.text ?: ("g" + (ctx.idi?.text?.toInt() ?: ++currentId))
        val r = Region(id)
        if (ctx.time() != null) {
            r.duration = ctx.time().accept(timeParser)
        }

        ctx.children.forEach {
            val tn = it.accept(this)
            if (tn != null) r.children.add(tn)
        }
        return r
    }


    fun rowId(ctx: TestTableLanguageParser.IntOrIdContext?): String =
            ctx?.id?.text ?: String.format("r%02d", ctx?.idi?.text?.toInt() ?: ++currentId)

    lateinit var currentRow: TableRow


    override fun visitRow(ctx: TestTableLanguageParser.RowContext): TableRow {
        val id = rowId(ctx.intOrId())
        currentRow = TableRow(id)
        currentRow.duration = ctx.time()?.accept(timeParser) ?: Duration.ClosedInterval(1, 1)

        ctx.rowInherit().forEach { it.accept(this) }

        ctx.kc().forEach {
            val id = it.IDENTIFIER()
            val fq = it.FQ_VARIABLE()
            if (id != null) {
                val name = id.text
                val run = 0
                currentRow.rawFields[gtt.getProgramVariables(name, run)] = it.cell()
            } else {
                val (run, name) = resolveName(fq, gtt)
                currentRow.rawFields[gtt.getProgramVariables(name, run)] = it.cell()
            }
        }

        if (gtt.options.relational) {
            ctx.controlCommands()?.accept(this)
        }

        if (ctx.goto_().isNotEmpty()) {
            currentRow.gotos = ctx.goto_().asSequence()
                    .flatMap { it.trans.asSequence() }
                    .map { visitGotoTransition(it) }
                    .toMutableList()
        }
        return currentRow
    }

    override fun visitRowInherit(ctx: TestTableLanguageParser.RowInheritContext): TableNode {
        val table = tables.find { ctx.name.text == it.name }
                ?: error("Could not find table ${ctx.name.text}.")

        val row = table.region.flat().find { it.id == ctx.rowId.text }
                ?: error("Could not find row ${ctx.rowId.text} in ${table.name}.")

        currentRow.rawFields += row.rawFields
        return currentRow
    }

    private fun visitGotoTransition(ctx: TestTableLanguageParser.GotoTransContext): GotoTransition {
        return GotoTransition(ctx.tblId.text, rowId(ctx.rowId),
                when {
                    ctx.MISS() != null -> GotoTransition.Kind.MISS
                    ctx.FAIL() != null -> GotoTransition.Kind.FAIL
                    else -> GotoTransition.Kind.PASS
                })
    }

    override fun visitControlPause(ctx: TestTableLanguageParser.ControlPauseContext): TableNode {
        ctx.intOrId().forEach { it ->
            val run = getProgramRun(it)
            val pause = ControlCommand.Pause(run)
            val play = ControlCommand.Play(run)
            if (play in currentRow.controlCommands) {
                currentRow.controlCommands.remove(play)
                info("Contradition with play-command in row ${currentRow.id}. Removing the play-command.")
            }
            currentRow.controlCommands.add(pause)
        }
        return currentRow
    }

    override fun visitControlPlay(ctx: TestTableLanguageParser.ControlPlayContext): TableNode {
        ctx.intOrId().forEach { it ->
            val run = getProgramRun(it)
            val pause = ControlCommand.Pause(run)
            val play = ControlCommand.Play(run)
            if (pause in currentRow.controlCommands) {
                currentRow.controlCommands.remove(pause)
                info("Contradition with pause-command in row ${currentRow.id}. Removing the pause-command.")
            }
            currentRow.controlCommands.add(play)
        }
        return currentRow
    }

    override fun visitControlBackward(ctx: TestTableLanguageParser.ControlBackwardContext): TableNode {
        val target = rowId(ctx.target)
        ctx.runs.forEach { it ->
            val run = getProgramRun(it)
            val backward = ControlCommand.Backward(run, target)
            val conflict = currentRow.controlCommands
                    .filterIsInstance<ControlCommand.Backward>()
                    .filter { it.affectedProgramRun == run }
            if (conflict.isNotEmpty())
                info("A backward-command already exists in row ${currentRow.id}. " +
                        "Removing the previous command.")
            currentRow.controlCommands.removeAll(conflict)
            currentRow.controlCommands.add(backward)
        }
        return currentRow
    }
}

class TimeParser(val timeConstants: Map<String, Int>) : TestTableLanguageParserBaseVisitor<Duration>() {

    fun accept(ctx: TestTableLanguageParser.IntOrConstContext): Int {
        if (ctx.INTEGER() != null) {
            return ctx.INTEGER().text.toInt()
        }

        val id = ctx.IDENTIFIER().text!!

        return timeConstants[id]
                ?: error("Error used time constant $id is not given. (no default or command option)")
    }

    override fun visitTimeSingleSided(ctx: TestTableLanguageParser.TimeSingleSidedContext): Duration {
        val lower = accept(ctx.intOrConst()) + if (ctx.op.text == ">") 1 else 0
        return Duration.OpenInterval(lower, accept(ctx.duration_flags()))
    }

    private fun accept(flags: TestTableLanguageParser.Duration_flagsContext?): DurationModifier {
        if (flags == null) return DurationModifier.NONE
        return if (flags.PFLAG() != null) {
            if (flags.INPUT() != null) DurationModifier.PFLAG_I
            else DurationModifier.PFLAG_IO
        } else if (flags.INPUT() != null) {
            DurationModifier.HFLAG_I
        } else {
            DurationModifier.HFLAG_IO
        }
    }

    override fun visitTimeClosedInterval(ctx: TestTableLanguageParser.TimeClosedIntervalContext): Duration {
        return Duration.ClosedInterval(
                accept(ctx.l),
                accept(ctx.u),
                accept(ctx.duration_flags()))
    }

    override fun visitTimeOpenInterval(ctx: TestTableLanguageParser.TimeOpenIntervalContext): Duration {
        return Duration.OpenInterval(accept(ctx.l), accept(ctx.duration_flags()))
    }

    override fun visitTimeFixed(ctx: TestTableLanguageParser.TimeFixedContext): Duration {
        val i = accept(ctx.intOrConst())
        return Duration.ClosedInterval(i, i)
    }

    override fun visitTimeDontCare(ctx: TestTableLanguageParser.TimeDontCareContext?): Duration = Duration.OpenInterval(0)

    override fun visitTimeOmega(ctx: TestTableLanguageParser.TimeOmegaContext) = Duration.Omega
}

internal fun resolveName(fqVariable: TerminalNode, current: GeneralizedTestTable): Pair<Int, String> =
        resolveName(fqVariable.text, current, Position.start(fqVariable.symbol))

//TODO Write tests
internal fun resolveName(fqVariable: String, current: GeneralizedTestTable, pos: Position? = null): Pair<Int, String> {
    require(current.options.relational) {
        "Full-qualified variable used in non-relational test table."
    }
    val parts = fqVariable.split("|>", "·", "::", limit = 2)
    val name = parts[parts.size - 1]


    val runNum = if (parts.size == 1) -1 else
        parts[0].toIntOrNull() ?: current.programRuns.indexOf(parts[0])
    require(runNum >= 0) {
        "No run is given for variable $name in $pos"
    }
    return runNum to name
}
