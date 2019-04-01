package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.analysis.*
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.TimeType
import edu.kit.iti.formal.automation.datatypes.values.TimeData
import edu.kit.iti.formal.automation.il.IlBody
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.operators.UnaryOperator
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.plcopenxml.IECXMLFacade
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.Utils
import edu.kit.iti.formal.automation.visitors.Visitable
import edu.kit.iti.formal.util.CodeWriter
import org.antlr.v4.runtime.*
import java.io.*
import java.lang.Byte.MAX_VALUE
import java.nio.charset.Charset
import java.nio.file.Path

/**
 * IEC61131Facade class.
 * @author Alexander Weigl
 * @since 27.11.16
 */
object IEC61131Facade {
    /**
     * Parse the given string into an expression.
     *
     * @param input an expression in Structured Text
     * @return The AST of the Expression
     */
    fun expr(input: CharStream): Expression {
        val parser = getParser(input)
        val ctx = parser.expression()
        val expr = ctx.accept(IECParseTreeToAST()) as Expression
        parser.errorReporter.throwException()
        return expr
    }

    fun expr(input: String): Expression {
        return expr(CharStreams.fromString(input))
    }

    fun getParser(input: CharStream): IEC61131Parser {
        val lexer = IEC61131Lexer(input)
        val p = IEC61131Parser(CommonTokenStream(lexer))
        p.errorListeners.clear()
        p.addErrorListener(p.errorReporter)
        return p
    }

    fun statements(input: CharStream): StatementList {
        val parser = getParser(input)
        val stmts = parser.statement_list().accept(IECParseTreeToAST()) as StatementList
        parser.errorReporter.throwException()
        return stmts
    }

    fun statements(input: String): StatementList = statements(CharStreams.fromString(input))

    fun file(input: CharStream): PouElements {
        val parser = getParser(input)
        val tle = parser.start().accept(IECParseTreeToAST()) as PouElements
        parser.errorReporter.throwException()
        return tle
    }


    fun file(path: Path, tee: File? = null): PouElements {
        return if (path.endsWith("xml")) {
            val out = IECXMLFacade.extractPLCOpenXml(path)
            if (tee != null) {
                tee.bufferedWriter().use {
                    it.write(out)
                }
                file(tee)
            } else {
                file(CharStreams.fromString(out, path.toString()))
            }
        } else
            file(CharStreams.fromPath(path))
    }


    @Throws(IOException::class)
    fun file(f: File, teeXmlParser: Boolean = true): PouElements {
        return if (f.extension == "xml") {
            val out = IECXMLFacade.extractPLCOpenXml(f.absolutePath)
            if (teeXmlParser) {
                val stfile = File(f.parentFile, f.nameWithoutExtension + ".st")
                stfile.bufferedWriter().use {
                    it.write(out)
                }
                file(CharStreams.fromFileName(stfile.absolutePath))
            } else {
                file(CharStreams.fromString(out, f.absolutePath))
            }
        } else
            file(CharStreams.fromFileName(f.absolutePath))

    }

    fun file(resource: InputStream) = file(CharStreams.fromStream(resource, Charset.defaultCharset()))

    fun getParser(s: String): IEC61131Parser {
        return getParser(CharStreams.fromString(s))
    }

    fun resolveDataTypes(elements: PouElements, scope: Scope = Scope.defaultScope()): Scope {
        val fdt = RegisterDataTypes(scope)
        val rdt = ResolveDataTypes(scope)
        val oo = ResolveOO(scope)
        //val rr = ResolveReferences(scope)
        elements.accept(EnsureFunctionReturnValue)
        elements.accept(fdt)
        elements.accept(rdt)
        elements.accept(RewriteEnums)
        elements.accept(MaintainInitialValues())
        elements.accept(oo)
        //elements.accept(rr)
        return scope
    }

    fun resolveDataTypes(scope: Scope = Scope.defaultScope(), vararg elements: Visitable): Scope {
        val fdt = RegisterDataTypes(scope)
        val rdt = ResolveDataTypes(scope)
        //val rr = ResolveReferences(scope)
        elements.forEach { it.accept(fdt) }
        elements.forEach { it.accept(rdt) }
        elements.forEach { it.accept(RewriteEnums) }
        elements.forEach { it.accept(MaintainInitialValues()) }
        //elements.accept(rr)
        return scope
    }

    fun fileResolve(input: List<CharStream>, builtins: Boolean = false): Pair<PouElements, List<ReporterMessage>> {
        val p = PouElements()
        input.forEach { p.addAll(file(it)) }
        if (builtins)
            p.addAll(BuiltinLoader.loadDefault())
        resolveDataTypes(p)
        return p to check(p)
    }

    fun fileResolve(input: CharStream, builtins: Boolean = false): Pair<PouElements, List<ReporterMessage>> = fileResolve(listOf(input), builtins)

    fun fileResolve(input: File, builtins: Boolean = false) = fileResolve(CharStreams.fromFileName(input.absolutePath), builtins)

    fun filefr(inputs: List<File>, builtins: Boolean = false) =
            fileResolve(inputs.map { CharStreams.fromFileName(it.absolutePath) }, builtins)


    /**
     *
     */
    fun readProgramsWithLibrary(libraryElements: List<File>, programs: List<File>): List<PouExecutable?> =
            readProgramsWithLibrary(libraryElements, programs, Utils::findProgram)


    /**
     *
     */
    fun readProgramsWithLibrary(libraryElements: List<File>, programs: List<File>, select: String): List<PouExecutable?> =
            readProgramsWithLibrary(libraryElements, programs) { seq ->
                seq.find { it.name == select } as? PouExecutable
            }

    /**
     *
     */
    fun readProgramsWithLibrary(libraryElements: List<File>,
                                programs: List<File>,
                                selector: (PouElements) -> PouExecutable?)
            : List<PouExecutable?> {
        return programs.map {
            val (elements, error) = IEC61131Facade.filefr(libraryElements + it)
            error.forEach { Console.warn(it.toHuman()) }
            selector(elements)
        }
    }

    /**
     *
     */
    fun check(p: PouElements): MutableList<ReporterMessage> {
        val r = Reporter()
        getCheckers(r).forEach { p.accept(it) }
        return r.messages
    }

    /**
     * Return the textual representation of the given AST.
     *
     * @param ast a [edu.kit.iti.formal.automation.st.ast.Top] object.
     * @return a [java.lang.String] object.
     */
    fun print(ast: Top, comments: Boolean = true): String {
        val sw = StringWriter()
        printTo(sw, ast, comments)
        return sw.toString()
    }

    fun printTo(stream: Writer, ast: Top, comments: Boolean = false) {
        val stp = StructuredTextPrinter(CodeWriter(stream))
        stp.isPrintComments = comments
        ast.accept(stp)
    }

    fun translateToSt(name: String, scope: Scope, sfc: SFCImplementation): StatementList {
        val st = StatementList()

        sfc.networks.forEach {
            //adding type xt and xinit to the scope
            if (!scope.dataTypes.containsKey("xt")) {
                scope.dataTypes.register("xinit", StructureTypeDeclaration("xinit",
                        listOf(VariableDeclaration("X", 8, SimpleTypeDeclaration("",
                                RefTo(null, null) , BooleanLit(true))),
                                VariableDeclaration("_X", AnyBit.BOOL), VariableDeclaration("T",
                                TimeType.TIME_TYPE), VariableDeclaration("_T", TimeType.TIME_TYPE))))
                scope.dataTypes.register("xt", StructureTypeDeclaration("xt",
                        listOf(VariableDeclaration("X", AnyBit.BOOL), VariableDeclaration("_X",
                                AnyBit.BOOL), VariableDeclaration("T", TimeType.TIME_TYPE),
                                VariableDeclaration("_T", TimeType.TIME_TYPE))))
            }
            //assigning a new x(ini)t variable for each step
            it.steps.forEach {
                if (!scope.variables.contains(it.name)) {
                    if (it.isInitial) {
                        scope.variables.add(VariableDeclaration(it.name, scope.resolveDataType("xinit")))
                    } else {
                        scope.variables.add(VariableDeclaration(it.name, scope.resolveDataType("xt")))
                    }
                }
            }
            //ordering the transitions by their source steps and priority
            val transitionsWithDuplicates = mutableListOf<SFCTransition>()
            it.steps.forEach {
                transitionsWithDuplicates.addAll(it.outgoing)
            }
            val transitions = transitionsWithDuplicates.distinct().sortedWith(
                    compareBy({ it.from.sortedBy { it.name }.toString() }, { MAX_VALUE - it.priority }))
            //generation of if branches for each transition
            var ifBranches = mutableListOf<GuardedStatement>()
            for (i in 0..(transitions.size-1)) {
                var transitionIf = BinaryExpression(SymbolicReference(
                        transitions[i].from.elementAt(0).name + ".X", null, null),
                        Operators.AND, transitions[i].guard)
                if (transitions[i].from.size > 1) {
                    for (j in 1..(transitions[i].from.size-1)) {
                        transitionIf = BinaryExpression(SymbolicReference(
                                transitions[i].from.elementAt(j).name + ".X", null, null),
                                Operators.AND, transitionIf)
                    }
                }
                var ifAssignments = StatementList()
                transitions[i].from.forEach {
                    ifAssignments.add(AssignmentStatement(SymbolicReference(it.name + "._X",
                            null, null), BooleanLit(false)))
                }
                transitions[i].to.forEach {
                    ifAssignments.add(AssignmentStatement(SymbolicReference(it.name + "._X",
                            null, null), BooleanLit(true)))
                    ifAssignments.add(AssignmentStatement(SymbolicReference(it.name + "._T",
                            null, null), TimeLit(TimeData())))
                }
                ifBranches.add(GuardedStatement(transitionIf, ifAssignments))
                ifAssignments.clear()
                if (!((i+1 != transitions.size) && transitions[i].from.equals(transitions[i+1].from))) {
                    st.add(IfStatement(ifBranches))
                    ifBranches.clear()
                }
            }
            //assignment and resetting
            transitions.forEach {
                st.add(AssignmentStatement(SymbolicReference(it.name + ".X", null, null),
                        SymbolicReference(it.name + "._X", null, null)))
                st.add(AssignmentStatement(SymbolicReference(it.name + ".T", null, null),
                        SymbolicReference(it.name + "._T", null, null)))
                st.add(AssignmentStatement(SymbolicReference(it.name + "._X", null, null),
                        BooleanLit(false)))
                st.add(AssignmentStatement(SymbolicReference(it.name + "._T", null, null),
                        TimeLit(TimeData())))
            }

            //listing all action blocks sorted by action names and qualifiers
            val actionBlocks = mutableListOf<Triple<String, SFCActionQualifier?, String>>()
            it.steps.forEach {
                var stepName = it.name
                it.events.forEach {
                    actionBlocks.add(Triple(it.actionName, it.qualifier, stepName))
                }
            }
            actionBlocks.sortedWith(compareBy({ it.first }, { it.second!!.qualifier.ordinal }))
            //generation of if branches for each time qualifier
            actionBlocks.forEach {
                if (it.second!!.hasTime()) {
                    if(!scope.variables.contains(it.first + "_T")) {
                        scope.variables.add(VariableDeclaration(it.first + "_T", TimeType.TIME_TYPE))
                    }
                    st.add(GuardedStatement(SymbolicReference(it.third + ".X", null, null),
                            StatementList(AssignmentStatement(SymbolicReference(it.first + "_T",
                                    null, null), it.second!!.time))))
                }
            }
            //evaluation of the action control function block parts
            var previous = Pair(listOf<SFCActionQualifier.Qualifier>(), listOf<String>())
            for (i in 0..(actionBlocks.size-1)) {
                previous = Pair(previous.first + actionBlocks[i].second!!.qualifier,
                        previous.second + actionBlocks[i].third)
                if ((i+1 == actionBlocks.size) || !(actionBlocks[i].first.equals(actionBlocks[i+1].first))) {
                    var qualifierExpr: Expression
                    scope.variables.add(VariableDeclaration(actionBlocks[i].first + "_Q", AnyBit.BOOL))
                    if (previous.first.contains(SFCActionQualifier.Qualifier.NON_STORED)) {
                        qualifierExpr = getStepsWithQualifier(previous, SFCActionQualifier.Qualifier.NON_STORED)
                        st.add(AssignmentStatement(SymbolicReference(actionBlocks[i].first + "_Q",
                                null, null), qualifierExpr))
                    }
                    if (previous.first.contains(SFCActionQualifier.Qualifier.SET)) {
                        scope.variables.add(VariableDeclaration(actionBlocks[i].first + "_S_FF",
                                scope.resolveDataType("RS")))
                        qualifierExpr = getStepsWithQualifier(previous, SFCActionQualifier.Qualifier.SET)
                        var setAssign = InvocationParameter("SET", false, qualifierExpr)
                        if (previous.first.contains(SFCActionQualifier.Qualifier.OVERRIDING_RESET)) {
                            qualifierExpr = getStepsWithQualifier(previous,
                                    SFCActionQualifier.Qualifier.OVERRIDING_RESET)
                        } else {
                            qualifierExpr = BooleanLit(false)
                        }
                        st.add(InvocationStatement(SymbolicReference(actionBlocks[i].first + "_S_FF",
                                null, null), mutableListOf(setAssign, InvocationParameter("RESET1",
                                false, qualifierExpr))))
                        st.add(AssignmentStatement(SymbolicReference(actionBlocks[i].first + "_Q",
                                null, null), BinaryExpression(SymbolicReference(
                                actionBlocks[i].first + "_Q", null, null),
                                Operators.OR, SymbolicReference(
                                actionBlocks[i].first + "_S_FF.Q1", null, null))))
                    }
                    if (previous.first.contains(SFCActionQualifier.Qualifier.TIME_LIMITED)) {
                        scope.variables.add(VariableDeclaration(actionBlocks[i].first + "_L_TMR",
                                scope.resolveDataType("TON")))
                        qualifierExpr = getStepsWithQualifier(previous, SFCActionQualifier.Qualifier.TIME_LIMITED)
                        st.add(InvocationStatement(SymbolicReference(actionBlocks[i].first + "_L_TMR",
                                null, null), mutableListOf(InvocationParameter("IN",
                                false, qualifierExpr), InvocationParameter("PT", false,
                                SymbolicReference(actionBlocks[i].first + "_T", null, null)))))
                        st.add(AssignmentStatement(SymbolicReference(actionBlocks[i].first + "_Q",
                                null, null), BinaryExpression(SymbolicReference(actionBlocks[i]
                                .first + "_Q", null, null), Operators.OR,
                                BinaryExpression(qualifierExpr, Operators.AND,
                                        UnaryExpression(UnaryOperator("NOT", AnyBit.BOOL), SymbolicReference(
                                                actionBlocks[i].first + "_L_TMR.Q", null, null))
                                ))))
                    }
                    if (previous.first.contains(SFCActionQualifier.Qualifier.STORE_DELAYED)) {
                        scope.variables.add(VariableDeclaration(actionBlocks[i].first + "_D_TMR",
                                scope.resolveDataType("TON")))
                        qualifierExpr = getStepsWithQualifier(previous, SFCActionQualifier.Qualifier.STORE_DELAYED)
                        st.add(InvocationStatement(SymbolicReference(actionBlocks[i].first + "_D_TMR",
                                null, null), mutableListOf(InvocationParameter("IN",
                                false, qualifierExpr), InvocationParameter("PT", false,
                                SymbolicReference(actionBlocks[i].first + "_T", null, null)))))
                        st.add(AssignmentStatement(SymbolicReference(actionBlocks[i].first + "_Q",
                                null, null), BinaryExpression(SymbolicReference(
                                actionBlocks[i].first + "_Q", null, null),
                                Operators.OR, SymbolicReference(
                                actionBlocks[i].first + "_D_TMR.Q", null, null))))
                    }
                    if (previous.first.contains(SFCActionQualifier.Qualifier.PULSE)) {
                        scope.variables.add(VariableDeclaration(actionBlocks[i].first + "_P_TRIG",
                                scope.resolveDataType("R_TRIG")))
                        qualifierExpr = getStepsWithQualifier(previous, SFCActionQualifier.Qualifier.PULSE)
                        st.add(InvocationStatement(SymbolicReference(actionBlocks[i].first + "_P_TRIG",
                                null, null), mutableListOf(InvocationParameter("CLK",
                                false, qualifierExpr))))
                        st.add(AssignmentStatement(SymbolicReference(actionBlocks[i].first + "_Q",
                                null, null), BinaryExpression(SymbolicReference(
                                actionBlocks[i].first + "_Q", null, null),
                                Operators.OR, SymbolicReference(
                                actionBlocks[i].first + "_P_TRIG.Q", null, null))))
                    }
                    if (previous.first.contains(SFCActionQualifier.Qualifier.STORE_AND_DELAY)) {
                        scope.variables.add(VariableDeclaration(actionBlocks[i].first + "_SD_FF",
                                scope.resolveDataType("RS")))
                        qualifierExpr = getStepsWithQualifier(previous, SFCActionQualifier.Qualifier.STORE_AND_DELAY)
                        var setAssign = InvocationParameter("SET", false, qualifierExpr)
                        if (previous.first.contains(SFCActionQualifier.Qualifier.OVERRIDING_RESET)) {
                            qualifierExpr = getStepsWithQualifier(previous,
                                    SFCActionQualifier.Qualifier.OVERRIDING_RESET)
                        } else {
                            qualifierExpr = BooleanLit(false)
                        }
                        st.add(InvocationStatement(SymbolicReference(actionBlocks[i].first + "_SD_FF",
                                null, null), mutableListOf(setAssign, InvocationParameter("RESET1",
                                false, qualifierExpr))))
                        scope.variables.add(VariableDeclaration(actionBlocks[i].first + "_SD_TMR",
                                scope.resolveDataType("TON")))
                        st.add(InvocationStatement(SymbolicReference(actionBlocks[i].first + "_SD_TMR",
                                null, null), mutableListOf(InvocationParameter("IN",
                                false, SymbolicReference(actionBlocks[i].first + "_SD_FF.Q1",
                                null, null)), InvocationParameter("PT", false,
                                SymbolicReference(actionBlocks[i].first + "_T", null, null)))))
                        st.add(AssignmentStatement(SymbolicReference(actionBlocks[i].first + "_Q",
                                null, null), BinaryExpression(SymbolicReference(
                                actionBlocks[i].first + "_Q", null, null),
                                Operators.OR, SymbolicReference(
                                actionBlocks[i].first + "_SD_TMR.Q", null, null))))
                    }
                    if (previous.first.contains(SFCActionQualifier.Qualifier.DELAYED_AND_STORED)) {
                        scope.variables.add(VariableDeclaration(actionBlocks[i].first + "_DS_TMR",
                                scope.resolveDataType("TON")))
                        qualifierExpr = getStepsWithQualifier(previous, SFCActionQualifier.Qualifier.DELAYED_AND_STORED)
                        st.add(InvocationStatement(SymbolicReference(actionBlocks[i].first + "_DS_TMR",
                                null, null), mutableListOf(InvocationParameter("IN",
                                false, qualifierExpr), InvocationParameter("PT", false,
                                SymbolicReference(actionBlocks[i].first + "_T", null, null)))))
                        scope.variables.add(VariableDeclaration(actionBlocks[i].first + "_DS_FF",
                                scope.resolveDataType("RS")))
                        if (previous.first.contains(SFCActionQualifier.Qualifier.OVERRIDING_RESET)) {
                            qualifierExpr = getStepsWithQualifier(previous,
                                    SFCActionQualifier.Qualifier.OVERRIDING_RESET)
                        } else {
                            qualifierExpr = BooleanLit(false)
                        }
                        st.add(InvocationStatement(SymbolicReference(actionBlocks[i].first + "_DS_FF",
                                null, null), mutableListOf(InvocationParameter("SET",
                                false, SymbolicReference(actionBlocks[i].first + "_DS_TMR.Q",
                                null, null)), InvocationParameter("RESET1",
                                false, qualifierExpr))))
                        st.add(AssignmentStatement(SymbolicReference(actionBlocks[i].first + "_Q",
                                null, null), BinaryExpression(SymbolicReference(
                                actionBlocks[i].first + "_Q", null, null),
                                Operators.OR, SymbolicReference(
                                actionBlocks[i].first + "_DS_FF.Q1", null, null))))
                    }
                    if (previous.first.contains(SFCActionQualifier.Qualifier.STORE_AND_LIMITED)) {
                        scope.variables.add(VariableDeclaration(actionBlocks[i].first + "_SL_FF",
                                scope.resolveDataType("RS")))
                        qualifierExpr = getStepsWithQualifier(previous, SFCActionQualifier.Qualifier.STORE_AND_LIMITED)
                        var setAssign = InvocationParameter("SET", false, qualifierExpr)
                        if (previous.first.contains(SFCActionQualifier.Qualifier.OVERRIDING_RESET)) {
                            qualifierExpr = getStepsWithQualifier(previous,
                                    SFCActionQualifier.Qualifier.OVERRIDING_RESET)
                        } else {
                            qualifierExpr = BooleanLit(false)
                        }
                        st.add(InvocationStatement(SymbolicReference(actionBlocks[i].first + "_SL_FF",
                                null, null), mutableListOf(setAssign, InvocationParameter("RESET1",
                                false, qualifierExpr))))
                        scope.variables.add(VariableDeclaration(actionBlocks[i].first + "_SL_TMR",
                                scope.resolveDataType("TON")))
                        st.add(InvocationStatement(SymbolicReference(actionBlocks[i].first + "_SL_TMR",
                                null, null), mutableListOf(InvocationParameter("IN",
                                false, SymbolicReference(actionBlocks[i].first + "_SL_FF.Q1",
                                null, null)), InvocationParameter("PT", false,
                                SymbolicReference(actionBlocks[i].first + "_T", null, null)))))
                        st.add(AssignmentStatement(SymbolicReference(actionBlocks[i].first + "_Q",
                                null, null), BinaryExpression(SymbolicReference(actionBlocks[i]
                                .first + "_Q", null, null), Operators.OR,
                                BinaryExpression(SymbolicReference(actionBlocks[i].first + "_SL_FF.Q1",
                                        null, null), Operators.AND,
                                        UnaryExpression(UnaryOperator("NOT", AnyBit.BOOL), SymbolicReference(
                                                actionBlocks[i].first + "_SL_TMR.Q", null, null)
                                        )))))
                    }
                    if (previous.first.contains(SFCActionQualifier.Qualifier.RAISING)) {
                        scope.variables.add(VariableDeclaration(actionBlocks[i].first + "_P1_TRIG",
                                scope.resolveDataType("R_TRIG")))
                        qualifierExpr = getStepsWithQualifier(previous, SFCActionQualifier.Qualifier.RAISING)
                        st.add(InvocationStatement(SymbolicReference(actionBlocks[i].first + "_P1_TRIG",
                                null, null), mutableListOf(InvocationParameter("CLK",
                                false, qualifierExpr))))
                        st.add(AssignmentStatement(SymbolicReference(actionBlocks[i].first + "_Q",
                                null, null), BinaryExpression(SymbolicReference(
                                actionBlocks[i].first + "_Q", null, null),
                                Operators.OR, SymbolicReference(
                                actionBlocks[i].first + "_P1_TRIG.Q", null, null))))
                    }
                    if (previous.first.contains(SFCActionQualifier.Qualifier.FALLING)) {
                        scope.variables.add(VariableDeclaration(actionBlocks[i].first + "_P0_TRIG",
                                scope.resolveDataType("F_TRIG")))
                        qualifierExpr = getStepsWithQualifier(previous, SFCActionQualifier.Qualifier.FALLING)
                        st.add(InvocationStatement(SymbolicReference(actionBlocks[i].first + "_P0_TRIG",
                                null, null), mutableListOf(InvocationParameter("CLK",
                                false, qualifierExpr))))
                        st.add(AssignmentStatement(SymbolicReference(actionBlocks[i].first + "_Q",
                                null, null), BinaryExpression(SymbolicReference(
                                actionBlocks[i].first + "_Q", null, null),
                                Operators.OR, SymbolicReference(
                                actionBlocks[i].first + "_P0_TRIG.Q", null, null))))
                    }
                    if (previous.first.contains(SFCActionQualifier.Qualifier.OVERRIDING_RESET)) {
                        qualifierExpr = getStepsWithQualifier(previous, SFCActionQualifier.Qualifier.OVERRIDING_RESET)
                        st.add(AssignmentStatement(SymbolicReference(actionBlocks[i].first + "_Q",
                                null, null), BinaryExpression(SymbolicReference(actionBlocks[i]
                                .first + "_Q", null, null), Operators.AND,
                                UnaryExpression(UnaryOperator("NOT", AnyBit.BOOL), qualifierExpr))))
                    }
                    previous = Pair(listOf(), listOf())
                }
            }
            //running the action/assigning the calculated boolean
            for (i in 0..(actionBlocks.size-1)) {
                if ((i + 1 == actionBlocks.size) || !(actionBlocks[i].first.equals(actionBlocks[i + 1].first))) {
                    if (scope.variables.contains(actionBlocks[i].first)) {
                        st.add(AssignmentStatement(SymbolicReference(actionBlocks[i].first, null, null),
                                SymbolicReference(actionBlocks[i].first + "_Q", null, null)))
                    } else {
                        st.add(GuardedStatement(SymbolicReference(actionBlocks[i].first + "_Q", null,
                                null), StatementList(InvocationStatement(SymbolicReference(actionBlocks[i].first,
                                null, null), mutableListOf()))))
                    }
                    st.add(AssignmentStatement(SymbolicReference(actionBlocks[i].first + "_Q", null,
                            null), BooleanLit(false)))
                }
            }
            //increasing the cycle time
            it.steps.forEach {
                st.add(GuardedStatement(SymbolicReference(it.name + ".X", null, null),
                        StatementList(AssignmentStatement(SymbolicReference(it.name + ".T", null,
                                null), BinaryExpression(SymbolicReference(it.name + ".T", null,
                                null), Operators.ADD, SymbolicReference("CYCLE_TIME", null,
                                null))))))
            }
        }
        return st
    }

    fun translateSfc(elements: PouElements) {
        elements.forEach {
            it.accept(TranslateSfcToSt)
        }
    }

    private fun getStepsWithQualifier(steps: Pair<List<SFCActionQualifier.Qualifier>, List<String>>,
                                      qualifier: SFCActionQualifier.Qualifier): Expression {
        var qualifierExpr: Expression
        qualifierExpr = SymbolicReference(steps.second[steps.first.indexOf(qualifier)] + ".X", null,
                null)
        if (steps.first.indexOf(qualifier) != steps.first.size - 1) {
            for (i in steps.first.indexOf(qualifier) + 1..(steps.first.size - 1)) {
                qualifierExpr = BinaryExpression(qualifierExpr, Operators.OR,
                        SymbolicReference(steps.second[steps.first.indexOf(qualifier)] + ".X", null,
                                null))
            }
        }
        return qualifierExpr
    }

    object InstructionList {
        /*
        fun getParser(input: Token): IlParser {
            return getParser(
                    CharStreams.fromString(input.text),
                    ShiftedTokenFactory(input))
        }
        fun getParser(input: CharStream, position: Position): IlParser {
            return getParser(input, ShiftedTokenFactory(position))
        }
        fun getParser(input: CharStream, tokenFactory: TokenFactory<*>? = null): IlParser {
            val lexer = IlLexer(input)
            if (tokenFactory != null)
                lexer.tokenFactory = tokenFactory
            val p = IlParser(CommonTokenStream(lexer))
            p.errorListeners.clear()
            p.addErrorListener(p.errorReporter)
            return p
        }
        fun parseBody(token: Token): IlBody {
            val ctx = getParser(token).ilBody()
            return ctx.accept(IlTransformToAst()) as IlBody
        }
        */


        fun parseBody(token: String): IlBody {
            val lexer = IEC61131Lexer(CharStreams.fromString(token))
            lexer.pushMode(1)
            val parser = IEC61131Parser(CommonTokenStream(lexer))
            val ctx = parser.ilBody()
            return ctx.accept(IECParseTreeToAST()) as IlBody
        }

        private class ShiftedTokenFactory(val offset: Int = 0,
                                          val offsetLine: Int = 0,
                                          val offsetChar: Int = 0) : CommonTokenFactory() {
            constructor(position: Position) : this(position.offset, position.lineNumber, position.charInLine)
            constructor(token: Token) : this(token.startIndex, token.line, token.charPositionInLine)

            override fun create(source: org.antlr.v4.runtime.misc.Pair<TokenSource, CharStream>?, type: Int, text: String?, channel: Int, start: Int, stop: Int, line: Int, charPositionInLine: Int): CommonToken {
                val token = super.create(source, type, text, channel, start, stop, line, charPositionInLine)
                token.startIndex += offset
                token.stopIndex += offset
                token.charPositionInLine += offsetChar
                token.line += offsetLine
                return token
            }
        }
    }
}