package edu.kit.iti.formal.automation.testtables


import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.EnumerationTypeDeclaration
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.testtables.builder.AutomataTransformerState
import edu.kit.iti.formal.automation.testtables.builder.AutomatonBuilderPipeline
import edu.kit.iti.formal.automation.testtables.builder.SMVConstructionModel
import edu.kit.iti.formal.automation.testtables.builder.SmvConstructionPipeline
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.io.TblLanguageToSmv
import edu.kit.iti.formal.automation.testtables.io.TestTableLanguageBuilder
import edu.kit.iti.formal.automation.testtables.io.TimeParser
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.automation.testtables.model.automata.AutomatonState
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.automation.testtables.model.automata.Transition
import edu.kit.iti.formal.automation.testtables.model.automata.TransitionType
import edu.kit.iti.formal.automation.testtables.print.DSLTablePrinter
import edu.kit.iti.formal.automation.testtables.viz.CounterExampleAnalyzer
import edu.kit.iti.formal.automation.testtables.viz.Mapping
import edu.kit.iti.formal.smv.*
import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SVariable
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.debug
import edu.kit.iti.formal.util.fail
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.io.File
import java.io.StringWriter

const val TABLE_SEP = "_"

object GetetaFacade {
    fun createParser(input: CharStream): TestTableLanguageParser {
        val lexer = TestTableLanguageLexer(input)
        val parser = TestTableLanguageParser(CommonTokenStream(lexer))

        lexer.removeErrorListeners()
        lexer.addErrorListener(parser.errorReporter)

        parser.removeErrorListeners()
        parser.addErrorListener(parser.errorReporter)

        return parser
    }

    fun createParser(input: String) = createParser(CharStreams.fromString(input))

    fun parseCell(cell: String, enableRelational: Boolean = true) =
            createParser(cell).also { it.relational = enableRelational }.cellEOF()!!

    fun exprToSMV(cell: String, column: SVariable, programRun: Int, vars: ParseContext): SMVExpr = exprToSMV(parseCell(cell, vars.relational).cell(), column, programRun, vars)

    fun exprToSMV(cell: TestTableLanguageParser.CellContext, column: SVariable,
                  programRun: Int, vars: ParseContext): SMVExpr {
        val ev = TblLanguageToSmv(column, programRun, vars)
        val expr = cell.accept(ev)
        debug("parsed: ${cell.text} to $expr")
        return expr
    }

    fun exprToSMV(u: TestTableLanguageParser.CellContext,
                  pv: ProjectionVariable, vc: ParseContext): SMVExpr {
        require(pv.arity != 0) { "Arity of column function is zero. Column ${pv.name}" }

        if (pv.arity > 1) {
            return when (u.chunk().first()) {
                is TestTableLanguageParser.CvariableContext -> {
                    val varName = u.chunk(0).text
                    val fd = vc.getFunction(varName)
                    return if (fd != null) {
                        check(fd.arity == pv.arity) {
                            "Arity mismatch in implicit function call $varName in column ${pv.name} "
                        }
                        fd.call(pv.argumentDefinitions)
                    } else
                        throw IllegalStateException("Multi-arity column header only supported with user-defined functions")
                }
                is TestTableLanguageParser.CdontcareContext -> SLiteral.TRUE
                else -> throw IllegalStateException("Multi-arity column header only supported with user-defined functions")
            }
        } else {
            return exprToSMV(u, pv.argumentDefinitions.first(), 0, vc)
        }
    }

    fun parseDuration(duration: String, timeConstants: Map<String, Int> = hashMapOf()): Duration {
        if (duration == "wait")//old attributes
            return Duration.OpenInterval(0)
        val parser = createParser(duration)
        val p = parser.time()
        return p.accept(TimeParser(timeConstants))
    }

    @Deprecated("use external/internalVariable")
    fun asSMVVariable(column: Variable): SVariable {
        return SVariable(column.name, getSMVDataType(column.dataType))
    }

    private fun getSMVDataType(dataType: AnyDt): SMVType {
        return DefaultTypeTranslator.INSTANCE.translate(dataType)
                ?: error("Data type $dataType is not supported by DataTypeTranslator")
    }

    val DEFAULT_COMPARISON_FUNCTIONS: Map<String, SmvFunctionDefinition> by lazy {
        val map = HashMap<String, SmvFunctionDefinition>()
        map["leq"] = getSmvFunction("x <= y", "x", "y")
        map["geq"] = getSmvFunction("x >= y", "x", "y")
        map["eq"] = getSmvFunction("x = y", "x", "y")
        map["neq"] = getSmvFunction("x != y", "x", "y")
        map["gt"] = getSmvFunction("x > y", "x", "y")
        map["lt"] = getSmvFunction("x < y", "x", "y")
        map
    }

    private fun getSmvFunction(body: String, vararg args: String): SmvFunctionDefinition {
        val sargs = args.map { SVariable(it) }
        return SmvFunctionDefinition(SMVFacade.expr(body), sargs)
    }

    val DEFAULT_PROGRAM_RUN_NAME = { it: Int -> "_$it$" }

    @JvmStatic
    fun parseTableDSL(input: String, timeConstants: Map<String, Int> = hashMapOf()) = parseTableDSL(CharStreams.fromString(input), timeConstants)

    @JvmStatic
    fun parseTableDSL(input: File, timeConstants: Map<String, Int> = hashMapOf()) = parseTableDSL(CharStreams.fromFileName(input.absolutePath), timeConstants)

    @JvmStatic
    fun parseTableDSL(input: CharStream,
                      timeConstants: Map<String, Int> = hashMapOf()): List<GeneralizedTestTable> {
        val parser = createParser(input)
        return parseTableDSL(parser.file(), timeConstants)
    }

    @JvmStatic
    fun parseTableDSL(ctx: TestTableLanguageParser.FileContext,
                      timeConstants: Map<String, Int> = hashMapOf()): List<GeneralizedTestTable> {
        val ttlb = TestTableLanguageBuilder(preDefinedTimeConstants = timeConstants)
        ctx.accept(ttlb)
        return ttlb.testTables
    }

    fun exprsToSMV(vc: ParseContext,
                   constraints: Map<ColumnVariable, TestTableLanguageParser.CellContext>)
            : Map<String, SMVExpr> = constraints.map { (t, u) ->
        if (t is ProgramVariable) {
            val n = t.internalVariable(vc.programRuns)//"${vc.programRuns[t.programRun]}${t.name}"
            n.name to exprToSMV(u, vc.getSMVVariable(t.programRun, t.name), t.programRun, vc)
        } else {
            t.name to exprToSMV(u, t as ProjectionVariable, vc)
        }
    }.toMap()


    fun getHistoryName(variable: SVariable, cycles: Int): String {
        return getHistoryName(variable) + "._$" + cycles
    }

    fun getHistoryName(variable: SVariable): String {
        return variable.name + "__history"
    }

    fun runNuXMV(nuXmvPath: String, folder: String,
                 modules: List<SMVModule>,
                 vt: VerificationTechnique): NuXMVOutput {
        val adapter = createNuXMVProcess(folder, modules, nuXmvPath, vt)
        return adapter.call()
    }

    fun createNuXMVProcess(folder: String, modules: List<SMVModule>,
                           nuXmvPath: String, vt: VerificationTechnique): NuXMVProcess {
        val outputFolder = File(folder)
        outputFolder.mkdirs()
        val moduleFile = File(outputFolder, "modules.smv")
        moduleFile.bufferedWriter().use { w ->
            val p = SMVPrinter(CodeWriter(w))
            modules.forEach { it.accept(p) }
        }
        val commandFile = File(folder, COMMAND_FILE)
        writeNuxmvCommandFile(vt.commands, commandFile)

        val adapter = NuXMVProcess(moduleFile, commandFile)
        adapter.executablePath = nuXmvPath
        adapter.workingDirectory = outputFolder
        return adapter
    }

    fun createSuperEnum(scopes: List<Scope>): EnumType {
        val allowedValues =
                scopes.flatMap { scope ->
                    scope.dataTypes.values()
                            .filter { it is EnumerationTypeDeclaration }
                            .map { it as EnumerationTypeDeclaration }
                            .flatMap { it.allowedValues.map { it.text } }
                }
        return EnumType(allowedValues)
    }

    fun generateInterface(name: String = "anonym",
                          scope: Scope = Scope.defaultScope(),
                          includeState: Boolean = true): String {
        val s = StringBuilder()
        s.append("table $name {\n")
        scope.filter { it.isInput }.forEach {
            s.append("\n\tvar input ${it.name} : ${it.dataType?.name}")
        }

        scope.filter { it.isOutput }.forEach {
            s.append("\n\tvar output ${it.name} : ${it.dataType?.name}")
        }

        if (includeState) {
            scope.filter { !it.isOutput && !it.isInput }.forEach {
                s.append("\n\tvar state input ${it.name} : ${it.dataType?.name} as ${it.name}_pre")
                s.append("\n\tvar state output ${it.name} : ${it.dataType?.name} as ${it.name}_post")
            }
        }

        s.append("\n\n\toptions{}")
        s.append("\n\n\tgroup{\n\t}")

        s.append("\n}")
        return s.toString()
    }

    fun readTables(file: File, timeConstants: Map<String, Int> = hashMapOf()): List<GeneralizedTestTable> {
        return parseTableDSL(file, timeConstants)
    }

    fun constructTable(table: GeneralizedTestTable) =
            AutomatonBuilderPipeline(table).transform()

    fun constructSMV(table: GeneralizedTestTable, superEnum: EnumType) =
            constructSMV(constructTable(table), superEnum)

    fun constructSMV(automaton: AutomataTransformerState, superEnum: EnumType) =
            SmvConstructionPipeline(automaton, superEnum).transform()

    fun analyzeCounterExample(automaton: TestTableAutomaton, testTable: GeneralizedTestTable, counterExample: CounterExample): MutableList<Mapping> {
        val analyzer = CounterExampleAnalyzer(automaton, testTable, counterExample,
                "_${testTable.name}")
        analyzer.run()
        return analyzer.rowMapping
    }

    fun print(gtt: GeneralizedTestTable): String {
        val stream = StringWriter()
        val p = DSLTablePrinter(CodeWriter(stream))
        p.print(gtt)
        return stream.toString()
    }

    fun functionToSmv(fd: FunctionDeclaration): SmvFunctionDefinition {
        val parameters = fd.scope.variables.filter { it.isInput }
                .map { DefaultTypeTranslator.INSTANCE.translate(it) }
        val body = SymbExFacade.evaluateFunction(fd, parameters)
        return SmvFunctionDefinition(body, parameters)
    }

    fun exprToSmv(expr: TestTableLanguageParser.ExprContext, parseContext: ParseContext): SMVExpr {
        val dummy = SVariable("dummy", SMVTypes.BOOLEAN)
        val visitor = TblLanguageToSmv(dummy, 0, parseContext)
        return expr.accept(visitor)
    }


    fun meshTables(tables: List<SMVConstructionModel>): TestTableAutomaton {
        val automaton = TestTableAutomaton()
        automaton.stateError = tables.first().automaton.stateError
        automaton.stateSentinel = tables.first().automaton.stateSentinel

        val jumpMap = HashMap<Pair<String, String>, AutomatonState>()

        //add all transition and rename the states to make them useable
        for (it in tables) {
            val a = it.automaton
            val tblName = it.testTable.name
            for ((row, states) in a.rowStates) {
                jumpMap[tblName to row.id] = states.first()

                //rename state id and row id
                states.forEach { it.name = "${tblName}${TABLE_SEP}${it.name}" }
                row.id = "${tblName}${TABLE_SEP}${row.id}"
                automaton.rowStates[row] = states
            }
            a.transitions.forEach { t ->
                val trans = t.copy( //rewrite the sentinel and error transitions
                        from = when (t.from) {
                            a.stateError -> automaton.stateError
                            a.stateSentinel -> automaton.stateSentinel
                            else -> t.from
                        },
                        to = when (t.to) {
                            a.stateError -> automaton.stateError
                            a.stateSentinel -> automaton.stateSentinel
                            else -> t.to
                        })
                automaton.transitions.add(trans)
            }
        }

        //remove transition, which goes to the sentinel with \pass, if there is a goto-pass command
        automaton.rowStates.filter { (a, _) ->
            a.gotos.any { it.kind == GotoTransition.Kind.PASS }
        }.forEach { (_, u) ->
            // _ ovewrites pass, so remove all transition from any state in u going to the sentinel
            automaton.transitions.removeIf { it.from in u && it.to == automaton.stateSentinel }
        }

        fun findTarget(gt: GotoTransition) =
                when {
                    gt.tableName == "eog" -> automaton.stateSentinel
                    gt.tableName == "err" -> automaton.stateError
                    else -> jumpMap[gt.tableName to gt.rowId]
                } ?: error("Could not find the table row ${gt.rowId} in table ${gt.tableName}.")


        //add goto commands into the table
        for (it in tables) {
            for ((row, states) in it.automaton.rowStates) {
                for (goto in row.gotos) {
                    val target = findTarget(goto)
                    for (s in states) {
                        if (s.optional) {
                            val type = when (goto.kind) {
                                GotoTransition.Kind.PASS ->
                                    if (s.progressFlag)
                                        TransitionType.ACCEPT_PROGRESS
                                    else
                                        TransitionType.ACCEPT
                                GotoTransition.Kind.MISS -> TransitionType.MISS
                                GotoTransition.Kind.FAIL -> TransitionType.FAIL
                            }
                            automaton.transitions.add(Transition("", s, target, type))
                        }
                    }
                }
            }
        }

        return automaton
    }

    /**
     * Creates a dummy gtt from a list of gtts.
     *
     * Useful for meshed gtts where a common signature is needed during the SMV construction.
     */
    fun createMeshedDummy(gtts: List<GeneralizedTestTable>): GeneralizedTestTable {
        val gtt = GeneralizedTestTable("__meshed__")
        gtt.programRuns = gtts.first().programRuns
        gtts.forEach {
            it.programVariables.forEach { v ->
                val c = gtt.programVariables.find { it.name == v.name }
                if (c == null) gtt.programVariables.add(v)
                else {
                    require(c.logicType == v.logicType) { "Data type clash for variable: $c and $v" }
                }
            }

            it.constraintVariables.forEach { cv ->
                val c = gtt.programVariables.find { it.name == cv.name }
                if (c == null) gtt.constraintVariables.add(cv)
                else {
                    fail("Clash of contraints variables: $cv ")
                }
            }
            gtt.functions.addAll(it.functions)
        }
        return gtt
    }

/*
    private class SuperEnumCreator : AstVisitor<Unit?>() {
        override fun defaultVisit(obj: Any): Unit? = null
        private val seq = ArrayList<String>()
        private val type = EnumType(seq)

        fun getType(): SMVType {
            return type
        }

        override fun visit(etd: EnumerationTypeDeclaration): Unit? {
            seq.addAll(etd.allowedValues.map { it.text })
            return null
        }
    }*/
}
