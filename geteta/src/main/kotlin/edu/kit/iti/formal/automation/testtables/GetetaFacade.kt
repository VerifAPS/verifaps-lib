package edu.kit.iti.formal.automation.testtables



import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.EnumerationTypeDeclaration
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.testtables.builder.AutomataTransformerState
import edu.kit.iti.formal.automation.testtables.builder.AutomatonBuilderPipeline
import edu.kit.iti.formal.automation.testtables.builder.SmvConstructionPipeline
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageLexer
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.io.TblLanguageToSmv
import edu.kit.iti.formal.automation.testtables.io.TestTableLanguageBuilder
import edu.kit.iti.formal.automation.testtables.io.TimeParser
import edu.kit.iti.formal.automation.testtables.model.*
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
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
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.io.File
import java.io.StringWriter

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
        debug("parsed: %s to %s", cell, expr)
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

    fun parseDuration(duration: String): Duration {
        if (duration == "wait")//old attributes
            return Duration.OpenInterval(0)
        val parser = createParser(duration)
        val p = parser.time()
        return p.accept(TimeParser())
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
    fun parseTableDSL(input: String) = parseTableDSL(CharStreams.fromString(input))

    @JvmStatic
    fun parseTableDSL(input: File) = parseTableDSL(CharStreams.fromFileName(input.absolutePath))

    @JvmStatic
    fun parseTableDSL(input: CharStream): List<GeneralizedTestTable> {
        val parser = createParser(input)
        return parseTableDSL(parser.file())
    }

    @JvmStatic
    fun parseTableDSL(ctx: TestTableLanguageParser.FileContext): List<GeneralizedTestTable> {
        val ttlb = TestTableLanguageBuilder()
        ctx.accept(ttlb)
        return ttlb.testTables
    }

    fun exprsToSMV(vc: ParseContext,
                   constraints: Map<ColumnVariable, TestTableLanguageParser.CellContext>)
            : Map<String, SMVExpr> = constraints.map { (t, u) ->
        if (t is ProgramVariable)
            t.name to exprToSMV(u, vc.getSMVVariable(t.programRun, t.name), t.programRun, vc)
        else //if(t is ProjectionVariable)
            t.name to exprToSMV(u, t as ProjectionVariable, vc)

    }.toMap()


    /*
    fun runNuXMV(folder: String, technique: VerificationTechnique, vararg modules: SMVModule): NuXMVOutput {
        return runNuXMV(folder, Arrays.asList(*modules), technique)
    }*/

    fun getHistoryName(variable: SVariable, cycles: Int): String {
        return getHistoryName(variable) + "._$" + cycles
    }

    fun getHistoryName(variable: SVariable): String {
        return variable.name + "__history"
    }

    fun runNuXMV(nuXmvPath: String, folder: String,
                 modules: List<SMVModule>,
                 vt: VerificationTechnique): NuXMVOutput {
        val outputFolder = File(folder)
        outputFolder.mkdirs()
        val moduleFile = File(outputFolder, "modules.smv")
        moduleFile.bufferedWriter().use { w ->
            val p = SMVPrinter(CodeWriter(w))
            modules.forEach { it.accept(p) }
        }
        val adapter = NuXMVProcess(moduleFile)
        adapter.executablePath = nuXmvPath
        adapter.workingDirectory = outputFolder
        adapter.commands = vt.commands
        return adapter.call()
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

    fun readTables(file: File): List<GeneralizedTestTable> {
        return parseTableDSL(file)
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
        val visitor = TblLanguageToSmv(dummy, null, parseContext)
        return expr.accept(visitor)
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
