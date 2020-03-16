package edu.kit.iti.formal.automation.testtables.builder

import edu.kit.iti.formal.automation.IEC61131Facade.fileResolve
import edu.kit.iti.formal.automation.SymbExFacade.simplify
import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.datatypes.FunctionBlockDataType
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.DefaultInitValue.getInit
import edu.kit.iti.formal.automation.st.HccPrinter
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.SpecialComment
import edu.kit.iti.formal.automation.st.Statements.ifthen
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st0.trans.SCOPE_SEPARATOR
import edu.kit.iti.formal.automation.testtables.GetetaFacade
import edu.kit.iti.formal.automation.testtables.GetetaFacade.constructTable
import edu.kit.iti.formal.automation.testtables.GetetaFacade.readTables
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.automation.testtables.model.automata.AutomatonState
import edu.kit.iti.formal.automation.testtables.model.automata.RowState
import edu.kit.iti.formal.automation.testtables.model.automata.TestTableAutomaton
import edu.kit.iti.formal.automation.testtables.model.automata.TransitionType
import edu.kit.iti.formal.automation.testtables.monitor.SMVToStVisitor
import edu.kit.iti.formal.automation.visitors.findFirstProgram
import edu.kit.iti.formal.smt.SmtEnumType
import edu.kit.iti.formal.smv.*
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.util.CodeWriter
import java.io.File
import java.io.PrintWriter

data class Miter(
        val scope: Scope,
        val init: StatementList,
        val body: StatementList,
        val functions: List<FunctionDeclaration>) {}

/**
 * Maps the value of a enum to its type.
 */
typealias EnumValueTable = Map<String, EnumerateType>

class GttMiterConstruction(val gtt: GeneralizedTestTable,
                           val automaton: TestTableAutomaton,
                           val enumValues: EnumValueTable,
                           val parentScope: Scope = Scope()) {
    private var transitions = automaton.transitions.groupBy { it.to }

    private fun createNext(state: AutomatonState): Expression {

        val expr =
                transitions[state]?.map { t ->
                    val stateVar = SVariable(t.from.name, SMVTypes.BOOLEAN)
                    if (t.type == TransitionType.TRUE) {
                        stateVar
                    } else {

                        val inputExpr = (t.from as RowState).row.inputExpr.values.conjunction(SLiteral.TRUE)
                        val outputExpr = (t.from as RowState).row.outputExpr.values.conjunction(SLiteral.TRUE)

                        when (t.type) {
                            TransitionType.ACCEPT ->
                                stateVar and inputExpr and outputExpr
                            TransitionType.ACCEPT_PROGRESS ->
                                stateVar and inputExpr and outputExpr
                            TransitionType.FAIL ->
                                stateVar and inputExpr and outputExpr.not()
                            TransitionType.MISS -> stateVar and inputExpr.not()
                            TransitionType.TRUE -> stateVar
                        }
                    }
                }?.disjunction() ?: SLiteral.FALSE
        return expr.translateToSt()
    }

    fun constructMiter(): Miter {
        val automaton = constructTable(gtt).automaton

        //Scope
        val fbScope = Scope(parentScope)

        gtt.programVariables.forEach { pv ->
            val vd = VariableDeclaration(pv.name, VariableDeclaration.INPUT, pv.dataType)
            if (pv.dataType is EnumerateType) {
                pv.dataType = INT
            }
            vd.initValue = getInit(pv.dataType)
            fbScope.variables.add(vd)
        }
        gtt.constraintVariables.forEach { cv ->
            val vd = VariableDeclaration(cv.name, VariableDeclaration.INPUT, cv.dataType)
            if (cv.dataType is EnumerateType) {
                cv.dataType = INT
            }

            if (false) { //TODO if cv ist already initialized
                //TODO initValue = ...
            }
            vd.initValue = getInit(cv.dataType)
            fbScope.variables.add(vd)
        }



        automaton.getRowStates().forEach { rowState ->
            val vd1 = VariableDeclaration(rowState.name, VariableDeclaration.LOCAL, AnyBit.BOOL)
            val vd2 = VariableDeclaration("_" + rowState.name, VariableDeclaration.LOCAL, AnyBit.BOOL)
            vd1.initValue = getInit(AnyBit.BOOL)
            vd2.initValue = getInit(AnyBit.BOOL)
            fbScope.variables.add(vd1)
            fbScope.variables.add(vd2)
        }

        val sentinel = VariableDeclaration(automaton.stateSentinel.name, VariableDeclaration.LOCAL, AnyBit.BOOL)
        sentinel.initValue = getInit(AnyBit.BOOL)
        fbScope.variables.add(sentinel)

        val err = VariableDeclaration("error", VariableDeclaration.LOCAL, AnyBit.BOOL)
        err.initValue = getInit(AnyBit.BOOL)
        fbScope.variables.add(err)

        val inv = VariableDeclaration("__INV__", VariableDeclaration.OUTPUT, AnyBit.BOOL)
//        inv.initValue = getInit(AnyBit.BOOL)
        fbScope.variables.add(inv)


        //Statements
        val stmts = StatementList()
        gtt.region.flat().forEach { tr ->
            automaton.getStates(tr)?.forEach { state ->
                val expr = createNext(state)
                val assign = "_${state.name}" assignTo expr
                stmts.add(assign)
            }
        }


        stmts.add(err.name assignTo createNext(automaton.stateError))
        stmts.add(sentinel.name assignTo createNext(automaton.stateSentinel))


        automaton.getRowStates().forEach { rowState ->
            stmts.add(rowState.name assignTo "_${rowState.name}")
        }


        val invassign: SMVExpr = automaton.getRowStates().toList()
                .map { SVariable(it.name, SMVTypes.BOOLEAN) }.disjunction().or(SVariable(sentinel.name, SMVTypes.BOOLEAN)).or(SVariable(err.name, SMVTypes.BOOLEAN).not())

        stmts.add("__INV__" assignTo invassign.translateToSt())


        val miterFb = FunctionBlockDeclaration(name = "miter", scope = fbScope, stBody = stmts)
        //Scope
        val scope = Scope()
        scope.variables.add(VariableDeclaration(miterFb.name, VariableDeclaration.LOCAL, FunctionBlockDataType(miterFb)))


        //Init
        val init = StatementList()
        if (gtt.constraintVariables.isNotEmpty()) {
            //haveoc
            val haveocConstraints = CommentStatement("haveoc constraints")
            val cVars = gtt.constraintVariables.map { VariableDeclaration("miter__${it.name}", it.dataType) }.toMutableList()
            haveocConstraints.setMetadata(SpecialComment::class.java, SpecialComment.HaveocComment(cVars))
            init.add(haveocConstraints)

            //assume
            val constraints = gtt.constraintVariables.map {
                GetetaFacade.exprToSMV(it.constraint!!, SVariable("miter__${it.name}"), 0, gtt.parseContext)
            }.conjunction(SLiteral.TRUE).translateToSt()

            val thenStmt = CommentStatement("assume constraints")
            thenStmt.setMetadata(SpecialComment::class.java,
                    SpecialComment.AssumeComment(constraints))

            init.add(ifthen(constraints.not(), thenStmt))
        }

        //Body
        val miterParams =
                miterFb.scope.variables.filter { it.isInput }.map {
                    InvocationParameter(it.name, false, SymbolicReference("program", SymbolicReference(it.name)))
                }.toMutableList()


        val miterInvoc = InvocationStatement(SymbolicReference(miterFb.name), miterParams)
        miterInvoc.invoked = Invoked.FunctionBlock(miterFb)
        val body = StatementList(miterInvoc)

        //Functions (empty)
        val funcs = mutableListOf<FunctionDeclaration>()
        return Miter(scope, init, body, funcs)
    }

    private fun SMVAst.translateToSt(): Expression = this.accept(ExpressionConversion(enumValues))
}

class ProgMiterConstruction(val pous: PouElements) {

    fun constructMiter(): Miter {

        val scope = Scope()
        val init = StatementList() //additional init
        val body = StatementList()
        val functions: MutableList<FunctionDeclaration> = mutableListOf()

        //////////////////////
        pous.forEach { pouE ->
            when (pouE) {
                is ProgramDeclaration -> {
                    val programFb = pouE.toFB()
                    //Scope
                    scope.variables.add(VariableDeclaration(programFb.name, VariableDeclaration.LOCAL, FunctionBlockDataType(programFb)))

                    pouE.scope.variables.filter { it.isInput }.forEach {
                        val vd = it.clone()
                        vd.type = VariableDeclaration.LOCAL
                        scope.variables.add(vd)
                    }

                    //TODO Scope -> Init ?

                    //Body
                    val vars = programFb.scope.variables.filter { it.isInput }.toMutableList()
                    var comm = "haveoc"
                    vars.forEach { comm += " ${it.name}" }
                    val commStmt = CommentStatement(comm)
                    commStmt.setMetadata(SpecialComment::class.java, SpecialComment.HaveocComment(vars))
                    body.add(commStmt)


                    val progParams =
                            programFb.scope.variables.filter { it.isInput }.map {
                                InvocationParameter(it.name, false, SymbolicReference(it.name))
                            }.toMutableList()


                    val programInvoc = InvocationStatement(SymbolicReference(programFb.name), progParams)
                    programInvoc.invoked = Invoked.FunctionBlock(programFb)
                    body.add(programInvoc)


                    return@forEach //only one Programdeclaration
                }
                is FunctionDeclaration ->
                    functions.add(pouE)
                is TypeDeclarations -> {
                    pouE.forEach { td ->
                        when (td) {
                            is EnumerationTypeDeclaration -> {

                                td.allowedValues.forEachIndexed { i, it ->
                                    val vd = VariableDeclaration(name = "${td.name}__${it.text.toUpperCase()}", type = VariableDeclaration.CONSTANT,
                                            td = SimpleTypeDeclaration(name = "", baseType = RefTo(INT), initialization = IntegerLit(i)))

                                    scope.add(vd)
                                }
                            }
                            else -> println("other TypeDeclaration")
                        }


                    }
                }
                else -> println("not a Program, Function or Typedeclarations")


                /////////////////////


            }
        }
        return Miter(scope, init, body, functions)
    }

    private fun ProgramDeclaration.toFB(): FunctionBlockDeclaration = FunctionBlockDeclaration(
            "program", scope, stBody, sfcBody, ilBody, fbBody, actions)
}

class ExpressionConversion(val enumValues: EnumValueTable) : SMVAstVisitor<Expression> {
    override fun visit(top: SMVAst): Expression {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(v: SVariable): Expression = SymbolicReference(v.name)
    override fun visit(be: SBinaryExpression): Expression = BinaryExpression(be.left.accept(this),
            SMVToStVisitor.operator(be.operator), be.right.accept(this))


    override fun visit(ue: SUnaryExpression): Expression = UnaryExpression(SMVToStVisitor.operator(ue.operator), ue.expr.accept(this))

    override fun visit(l: SLiteral): Expression {
        return when (l.dataType) {
            is SMVTypes.BOOLEAN -> BooleanLit(l.value == true)
            is SMVWordType -> IntegerLit(INT, l.value.toString().toBigInteger())
            is EnumType -> {
                val et = enumValues[l.value.toString().toUpperCase()]
                        ?: error("No enum defined which contains ${l.value}. Defined values: ${enumValues.keys}")
                EnumLit(et, l.value.toString())
            }
            else -> error("Literals of type '${l.javaClass} are not supported")
        }
    }

    override fun visit(a: SAssignment): Expression {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(ce: SCaseExpression): Expression {
        fun ifThenElse(cases: List<SCaseExpression.Case>, n: Int): Expression {
            if (n >= cases.size) {
                throw IllegalArgumentException()
            }

            if (n == cases.size - 1) {//last element
                // ignoring the last condition for well-definedness
                return cases[n].then.accept(this)
            }

            val ite = Invocation("SEL",
                    cases[n].condition.accept(this),
                    cases[n].then.accept(this),
                    ifThenElse(cases, n + 1))
            return ite
        }
        return ifThenElse(ce.cases, 0)
    }

    override fun visit(smvModule: SMVModule): Expression {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun visit(func: SFunction): Expression {
        return Invocation(func.name,
                func.arguments.map { it.accept(this) }
        )
    }


    override fun visit(quantified: SQuantified): Expression {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }
}

open class ProgramCombination(val program: Miter, val miter: Miter) {

    fun combine(): PouElements {

        //Scope
        val scope = Scope()
        scope.addVariables(program.scope)
        scope.addVariables(miter.scope)


        //Body
        val body = StatementList()

        body.addAll(program.init)
        body.addAll(miter.init)

        //while
        val whileBody = StatementList()

        whileBody.addAll(program.body)
        whileBody.addAll(miter.body)


        val assert = CommentStatement("assert __INV__")
        assert.setMetadata(SpecialComment::class.java, SpecialComment.AssertComment(SymbolicReference("miter____INV__")))
        whileBody.add(assert)


        //end while


        body.add(WhileStatement(BooleanLit.LTRUE, whileBody))
        //end program

//        //haveoc-functions TODO
//        val hiScope = Scope()
//        hiScope.add(VariableDeclaration("inout", VariableDeclaration.INOUT, INT))
//        hiScope.add(VariableDeclaration("nondet", VariableDeclaration.LOCAL, INT))
//        val hiBody = StatementList()
//        hiBody.add(AssignmentStatement(SymbolicReference("nondet"), SymbolicReference("_")))
//        hiBody.add(AssignmentStatement(SymbolicReference("inout"), SymbolicReference("nondet")))
//        val haveocIntFunDec = FunctionDeclaration("haveoc_int", hiScope, RefTo(INT), hiBody)


        val elems = PouElements()
//        elems.add(haveocIntFunDec)
        elems.addAll(program.functions)
        elems.addAll(miter.functions)
        elems.add(ProgramDeclaration(name = "combinedProgram", scope = scope, stBody = body))

        return simplify(elems)

    }


    private fun ProgramDeclaration.toFB(): FunctionBlockDeclaration = FunctionBlockDeclaration(
            name, scope, stBody, sfcBody, ilBody, fbBody, actions)


}


fun main() = run {
    SCOPE_SEPARATOR = "__"
    //choose gtt
    run("geteta/examples/MinMax/MinMax.st",
            "geteta/examples/MinMax/MinMax.gtt")

    // val stCycles = File("c:/Users/User/Documents/studium/ws_1920/Bachelorarbeit/verifaps/verifaps-lib/geteta/examples/cycles/cycles.st")
    // val stConst = File("c:/Users/User/Documents/studium/ws_1920/Bachelorarbeit/verifaps/verifaps-lib/geteta/examples/constantprogram/constantprogram.st")
    // val stLinRe = File("c:/Users/User/Documents/studium/ws_1920/Bachelorarbeit/verifaps/verifaps-lib/geteta/examples/LinRe/lr.st")
    // val gttCycles = File("c:/Users/User/Documents/studium/ws_1920/Bachelorarbeit/verifaps/verifaps-lib/geteta/examples/cycles/cycles.tt.txt")
    // val gttConst = File("c:/Users/User/Documents/studium/ws_1920/Bachelorarbeit/verifaps/verifaps-lib/geteta/examples/constantprogram/constantprogram_broken.gtt")
    // val gttMinMax_broken = File("c:/Users/User/Documents/studium/ws_1920/Bachelorarbeit/verifaps/verifaps-lib/geteta/examples/MinMax/MinMax_Broken.gtt")
    // val gttLinRe = File("c:/Users/User/Documents/studium/ws_1920/Bachelorarbeit/verifaps/verifaps-lib/geteta/examples/LinRe/lr.tt")
}

fun run(program: String, table: String) {
    //region read table
    val gtt = readTables(File(table)).first()
    gtt.programRuns = listOf("")
    gtt.generateSmvExpression()
    val gttAsAutomaton = constructTable(gtt).automaton
    //endregion

    //region read program
    val progs = fileResolve(File(program)).first
    //endprogram

    /* PrintWriter(System.out).use { out ->
         val fb = FunctionBlockDeclaration(name = "miter", scope = miter.scope, stBody = miter.statements)
         IEC61131Facade.printTo(out, fb)
     }*/
    val enum = progs.findFirstProgram()?.scope?.enumValuesToType() ?: mapOf()
    val mc = GttMiterConstruction(gtt, gttAsAutomaton, enum)
    val miter = mc.constructMiter()
    val productProgram = ProgramCombination(ProgMiterConstruction(progs).constructMiter(), miter).combine()

    PrintWriter(System.out).use { out ->
        //            IEC61131Facade.printTo(out, simplify(combi), true)
        val hccprinter = HccPrinter(CodeWriter(out))
        hccprinter.isPrintComments = true
        productProgram.accept(hccprinter)

    }

    //region Sandbox------------------------------

//        val body = StatementList()
//        val cc: CaseCondition = CaseCondition.IntegerCondition(IntegerLit(INT, 1.toString().toBigInteger()))
//        val ccArray = arrayListOf<CaseCondition>(cc)
//        val sl = StatementList()
//        sl.add(CommentStatement("Some"))
//
//        sl.add(CommentStatement("Code Block"))
//
//
//        body.add(ForStatement(variable = "counter", start = IntegerLit(0),
//                stop = IntegerLit(20), step = IntegerLit(2), statements = sl))
//
//
//
//        val scope = Scope()
//        val decl = VariableDeclaration(name = "1simpletypedecl", type = VariableDeclaration.LOCAL, td = SimpleTypeDeclaration(name = "simpletd", baseType = RefTo(AnyBit.BOOL), initialization = IntegerLit(1)))
//        scope.add(decl)
//
//        println("TypeDecl: ${decl.typeDeclaration}")
//        println("Type: ${decl.type}")
//        println("Datatype: ${decl.dataType}")
//        println("init: ${decl.init}")
//        println("initValue: ${decl.initValue?.value}")
//
//        val decl2 = VariableDeclaration(name = "2simpletypedecl", type = VariableDeclaration.LOCAL, td = SimpleTypeDeclaration(name = "simpletd", baseType = RefTo(INT), initialization = IntegerLit(1)))
//        scope.add(decl2)
//        val decl3 = VariableDeclaration(name = "3simpletypedecl", type = VariableDeclaration.LOCAL, td = SimpleTypeDeclaration(name = "simpletd", baseType = RefTo(AnyBit.BOOL), initialization = BooleanLit.LTRUE))
//
//        scope.add(decl3)
//
//
//        val pd = ProgramDeclaration(name = "testingStuff", scope = scope, stBody = body)


    //endregion Sandbox_end-------------------------------
}