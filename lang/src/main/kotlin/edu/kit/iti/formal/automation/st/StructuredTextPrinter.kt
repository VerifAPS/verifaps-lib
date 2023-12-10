package edu.kit.iti.formal.automation.st

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.datatypes.IECString
import edu.kit.iti.formal.automation.datatypes.values.ReferenceValue
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.il.IlPrinter
import edu.kit.iti.formal.automation.operators.Operator
import edu.kit.iti.formal.automation.operators.UnaryOperator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitor
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.joinInto
import java.util.*

/**
 * Created by weigla on 15.06.2014.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
open class StructuredTextPrinter(var sb: CodeWriter = CodeWriter()) : AstVisitor<Unit>() {
    private val literals: StringLiterals = SL_ST
    var bodyPrintingOrder = listOf(BodyPrinting.ST, BodyPrinting.SFC, BodyPrinting.IL)
    var isPrintComments: Boolean = false

    val string: String
        get() = sb.toString()


    override fun defaultVisit(obj: Any) {
        throw IllegalArgumentException("not implemented: " + obj::class.java)
    }

    override fun visit(blockStatement: BlockStatement) {
        sb.nl().print("//! REGION ${blockStatement.name}")
        blockParam(blockStatement.state, "[", "]")
        blockParam(blockStatement.input, "(", ")")
        sb.write(" => ")
        blockParam(blockStatement.output, "(", ")")
        sb.increaseIndent()
        blockStatement.statements.accept(this)
        sb.decreaseIndent()
        sb.nl().print("//! END_REGION")
    }

    private fun blockParam(p: MutableList<SymbolicReference>, pre: String, suf: String) =
            p.joinInto(sb, ", ", pre, suf) {
                it.accept(this@StructuredTextPrinter)
            }


    override fun visit(empty: EMPTY_EXPRESSION) {
        sb.print("(* empty expression *)")
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration) {
        sb.printf("ARRAY[")
        arrayTypeDeclaration.ranges.forEachIndexed { i, it ->
            it.start.accept(this)
            sb.printf("..")
            it.stop.accept(this)
            if (i < arrayTypeDeclaration.ranges.size - 1)
                sb.printf(", ")
        }
        sb.printf("] OF ")
        sb.printf(arrayTypeDeclaration.baseType.identifier ?: "<missing>")
    }

    override fun visit(stringTypeDeclaration: StringTypeDeclaration) {
        sb.printf("STRING")
    }

    override fun visit(elements: PouElements) {
        elements.forEach { it.accept(this) }
    }


    override fun visit(exitStatement: ExitStatement) {
        sb.printf(literals.exit()).printf(literals.statement_separator())

    }


    override fun visit(integerCondition: CaseCondition.IntegerCondition) {
        sb.appendIdent()
        integerCondition.value.accept(this)

    }


    override fun visit(enumeration: CaseCondition.Enumeration) {
        if (enumeration.start == enumeration.stop) {
            enumeration.start.accept(this)
        } else {
            enumeration.start.accept(this)
            sb.printf("..")
            enumeration.stop!!.accept(this)
        }


    }


    override fun visit(binaryExpression: BinaryExpression) {
        sb.append('(')
        binaryExpression.leftExpr.accept(this)
        sb.printf(" ").printf(literals.operator(binaryExpression.operator)).printf(" ")
        binaryExpression.rightExpr.accept(this)
        sb.append(')')

    }


    override fun visit(assignmentStatement: AssignmentStatement) {
        sb.nl()
        assignmentStatement.location.accept(this)
        if (assignmentStatement.isAssignmentAttempt)
            sb.printf(literals.assignmentAttempt())
        else
            sb.printf(literals.assign())
        assignmentStatement.expression.accept(this)
        sb.printf(";")
    }


    override fun visit(configurationDeclaration: ConfigurationDeclaration) {

    }


    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
        sb.nl().printf(enumerationTypeDeclaration.name).printf(" : ")
        enumerationTypeDeclaration.allowedValues.joinTo(sb, ", ", "(", ");") {
            it.text
        }
    }

    override fun visit(init: IdentifierInitializer) {
        sb.printf(init.value!!)

    }


    override fun visit(repeatStatement: RepeatStatement) {
        sb.nl()
        sb.printf("REPEAT").increaseIndent()
        repeatStatement.statements.accept(this)

        sb.decreaseIndent().nl().printf("UNTIL ")
        repeatStatement.condition.accept(this)
        sb.printf("END_REPEAT")

    }


    override fun visit(whileStatement: WhileStatement) {
        sb.nl()
        sb.printf("WHILE ")
        whileStatement.condition.accept(this)
        sb.printf(" DO ").increaseIndent()
        whileStatement.statements.accept(this)
        sb.decreaseIndent().nl()
        sb.printf("END_WHILE")

    }


    override fun visit(unaryExpression: UnaryExpression) {
        sb.printf(literals.operator(unaryExpression.operator)!!).printf(" ")
        unaryExpression.expression.accept(this)

    }


    override fun visit(typeDeclarations: TypeDeclarations) {

        if (typeDeclarations.size > 0) {
            sb.printf("TYPE ").increaseIndent()
            for (decl in typeDeclarations) {
                decl.accept(this)
            }
            sb.decreaseIndent().nl().printf("END_TYPE").nl().nl()
        }

    }

    override fun visit(caseStatement: CaseStatement) {
        sb.nl().printf("CASE ")
        caseStatement.expression.accept(this)
        sb.printf(" OF ").increaseIndent()

        for (c in caseStatement.cases) {
            c.accept(this)
            sb.nl()
        }

        if (caseStatement.elseCase!!.size > 0) {
            sb.nl().printf("ELSE ")
            caseStatement.elseCase!!.accept(this)
        }

        sb.nl().decreaseIndent().appendIdent().printf("END_CASE")

    }

    override fun visit(symbolicReference: SymbolicReference) {
        sb.printf(quoteIdentifier(symbolicReference.identifier))

        for (i in 0 until symbolicReference.derefCount)
            sb.printf("^")

        if (symbolicReference.subscripts != null && !symbolicReference.subscripts!!.isEmpty()) {
            symbolicReference.subscripts!!.joinInto(sb, ", ", "[", "]") { it.accept(this) }
        }

        if (symbolicReference.sub != null) {
            sb.printf(".")
            symbolicReference.sub!!.accept(this)
        }


    }

    val QUOTED_IDENTIFIER = listOf("STEP", "END_STEP", "TRANSITION", "END_TRANSITION", "INITIAL_STEP", "FROM")
    private fun quoteIdentifier(identifier: String): String {
        return if (identifier.uppercase(Locale.getDefault()) in QUOTED_IDENTIFIER) {
            "`$identifier`"
        } else {
            identifier
        }
    }


    override fun visit(statements: StatementList) {
        for (stmt in statements) {
            stmt.accept(this)
        }

    }


    override fun visit(programDeclaration: ProgramDeclaration) {
        printComment(programDeclaration.comment)
        sb.printf("PROGRAM ").printf(programDeclaration.name).increaseIndent()
        programDeclaration.scope.accept(this)

        sb.nl()

        if (!programDeclaration.actions.isEmpty()) {
            programDeclaration.actions.forEach { v -> v.accept(this) }
            sb.nl()
        }

        printBody(programDeclaration)

        sb.decreaseIndent().nl().printf("END_PROGRAM").nl()
    }


    override fun visit(expressions: ExpressionList) {
        expressions.joinInto(sb) { it.accept(this) }
    }


    override fun visit(invocation: Invocation) {
        invocation.callee.accept(this)
        visitInvocationParameter(invocation.parameters)
    }

    private fun visitInvocationParameter(parameters: MutableList<InvocationParameter>) {
        parameters.joinInto(sb, ", ", "(", ")") {
            if (it.name != null) {
                sb.printf(it.name!!)
                if (it.isOutput)
                    sb.printf(" => ")
                else
                    sb.printf(" := ")
            }
            it.expression.accept(this)
        }
    }


    override fun visit(forStatement: ForStatement) {
        sb.nl()
        sb.printf("FOR ").printf(forStatement.variable)
        sb.printf(" := ")
        forStatement.start.accept(this)
        sb.printf(" TO ")
        forStatement.stop.accept(this)
        sb.printf(" DO ").increaseIndent()
        forStatement.statements.accept(this)
        sb.decreaseIndent().nl()
        sb.printf("END_FOR")

    }


    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        printComment(functionBlockDeclaration.comment)
        sb.printf("FUNCTION_BLOCK ")
        if (functionBlockDeclaration.isFinal)
            sb.printf("FINAL ")
        if (functionBlockDeclaration.isAbstract)
            sb.printf("ABSTRACT ")

        sb.printf(functionBlockDeclaration.name)

        if (functionBlockDeclaration.parent.identifier != null) {
            sb.printf(" EXTENDS ").printf(functionBlockDeclaration.parent.identifier!!)
        }

        if (functionBlockDeclaration.interfaces.isNotEmpty()) {
            val interf = functionBlockDeclaration.interfaces
                    .map { it.identifier!! }
                    .joinToString(", ")
            sb.printf(" IMPLEMENTS ").printf(interf)
        }
        sb.increaseIndent().nl()
        functionBlockDeclaration.scope.accept(this)
        sb.nl()

        if (functionBlockDeclaration.methods.isNotEmpty()) {
            functionBlockDeclaration.methods.forEach { it.accept(this) }
            sb.nl()
        }

        if (!functionBlockDeclaration.actions.isEmpty()) {
            functionBlockDeclaration.actions.forEach { v -> v.accept(this) }
        }

        printBody(functionBlockDeclaration)

        sb.decreaseIndent().nl().printf("END_FUNCTION_BLOCK").nl().nl()

    }

    private fun printComment(comment: String) {
        if (comment.isNotBlank()) {
            sb.printf(literals.comment_open())
            sb.printf(comment)
            sb.printf(literals.comment_close() + "\n")
        }
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration) {
        sb.printf("INTERFACE ").printf(interfaceDeclaration.name)

        val extendsInterfaces = interfaceDeclaration.interfaces.map { it.identifier }
        if (!extendsInterfaces.isEmpty())
            sb.printf(" EXTENDS ").print(extendsInterfaces)

        sb.increaseIndent().nl()

        //interfaceDeclaration.scope.accept(this)

        interfaceDeclaration.methods.forEach { m -> m.accept(this) }

        sb.decreaseIndent().nl().printf("END_INTERFACE").nl().nl()

    }

    override fun visit(clazz: ClassDeclaration) {
        printComment(clazz.comment)
        sb.printf("CLASS ")

        if (clazz.isFinal)
            sb.printf("FINAL ")
        if (clazz.isAbstract)
            sb.printf("ABSTRACT ")

        sb.printf(clazz.name)

        val parent = clazz.parent.identifier
        if (parent != null)
            sb.printf(" EXTENDS ").printf(parent)

        val interfaces = clazz.interfaces.map { it.identifier }
        if (!interfaces.isEmpty())
            sb.printf(" IMPLEMENTS ").printf(interfaces.joinToString(","))

        sb.increaseIndent().nl()

        clazz.scope.accept(this)

        clazz.methods.forEach { m -> m.accept(this) }

        sb.decreaseIndent().nl().printf("END_CLASS").nl().nl()

    }

    override fun visit(method: MethodDeclaration) {
        sb.printf("METHOD ")

        if (method.isFinal)
            sb.printf("FINAL ")
        if (method.isAbstract)
            sb.printf("ABSTRACT ")
        if (method.isOverride)
            sb.printf("OVERRIDE ")

        sb.printf(method.accessSpecifier.toString() + " ")

        sb.printf(method.name)

        val returnType = method.returnTypeName
        if (!returnType!!.isEmpty())
            sb.printf(" : $returnType")

        sb.increaseIndent().nl()

        method.scope.accept(this)

        method.stBody.accept(this)

        sb.decreaseIndent().nl().printf("END_METHOD").nl().nl()

    }

    override fun visit(functionDeclaration: FunctionDeclaration) {
        printComment(functionDeclaration.comment)
        sb.printf("FUNCTION ").printf(functionDeclaration.name)

        val returnType = functionDeclaration.returnType.identifier
        if (!(returnType == null || returnType.isEmpty()))
            sb.printf(" : $returnType")

        sb.increaseIndent().nl()

        functionDeclaration.scope.accept(this)

        printBody(functionDeclaration)

        sb.decreaseIndent().nl().printf("END_FUNCTION").nl().nl()

    }

    override fun visit(gvlDecl: GlobalVariableListDeclaration) {
        gvlDecl.scope.accept(this)
        sb.nl()

    }

    override fun visit(referenceSpecification: ReferenceTypeDeclaration) {
        sb.printf("REF_TO ")
        referenceSpecification.refTo.accept(this)
    }

    override fun visit(referenceValue: ReferenceValue) {
        sb.printf("REF(")
        referenceValue.referenceTo.accept(this)
        sb.printf(")")

    }


    override fun visit(returnStatement: ReturnStatement) {
        sb.nl().printf("RETURN;")
    }


    override fun visit(ifStatement: IfStatement) {
        for (i in 0 until ifStatement.conditionalBranches.size) {
            sb.nl()

            if (i == 0)
                sb.printf("IF ")
            else
                sb.printf("ELSIF ")

            ifStatement.conditionalBranches[i].condition.accept(this)

            sb.printf(" THEN").increaseIndent()
            ifStatement.conditionalBranches[i].statements.accept(this)
            sb.decreaseIndent()
        }

        if (ifStatement.elseBranch.size > 0) {
            sb.nl().printf("ELSE").increaseIndent()
            ifStatement.elseBranch.accept(this)
            sb.decreaseIndent()
        }
        sb.nl().printf("END_IF")

    }

    override fun visit(actionDeclaration: ActionDeclaration) {
        sb.nl().printf("ACTION ").printf(actionDeclaration.name).increaseIndent()
        printBody(actionDeclaration)
        sb.decreaseIndent().nl().printf("END_ACTION")

    }


    override fun visit(invocation: InvocationStatement) {
        sb.nl()
        invocation.callee.accept(this)
        visitInvocationParameter(invocation.parameters)
        sb.printf(";")
    }


    override fun visit(aCase: Case) {
        sb.nl()
        aCase.conditions.joinInto(sb) { it.accept(this) }
        sb.printf(":")
        sb.block() {
            aCase.statements.accept(this@StructuredTextPrinter)
        }
    }


    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration) {
        sb.printf(simpleTypeDeclaration.baseType.identifier!!)
        /*if (simpleTypeDeclaration.initialization != null) {
            sb.printf(" := ")
            simpleTypeDeclaration.initialization!!.accept(this)
        }*/
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration) {
        sb.printf(structureTypeDeclaration.name)
        sb.printf(": STRUCT").nl().increaseIndent()
        structureTypeDeclaration.fields.forEach { it ->
            sb.nl()
            it.accept(this)
        }
        sb.decreaseIndent().printf("END_STRUCT;").nl()

    }

    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration) {
        sb.printf(subRangeTypeDeclaration.name)
        sb.printf(": ").printf(subRangeTypeDeclaration.baseType.identifier!!)
        sb.printf("(")
        subRangeTypeDeclaration.range!!.start.accept(this)
        sb.printf(" .. ")
        subRangeTypeDeclaration.range!!.stop.accept(this)
        sb.printf(")")
        /*if (subRangeTypeDeclaration.initialization != null) {
            sb.printf(" := ")
            subRangeTypeDeclaration.initialization!!.accept(this)
        }*/
        sb.printf(";")

    }

    override fun visit(vd: VariableDeclaration) {
        sb.write("${vd.name} :")
        variableDataType(vd)
    }

    val variableDeclarationUseDataType = false
    private fun variableDataType(vd: VariableDeclaration) {
        val dt = vd.dataType
        if (variableDeclarationUseDataType && dt != null) {
            variableDataType(dt)
        } else {
            vd.typeDeclaration?.accept(this)
        }
    }

    fun variableDataType(dt: AnyDt) {
        sb.printf(dt.reprDecl())
    }


    override fun visit(commentStatement: CommentStatement) {
        if (isPrintComments) {
            sb.nl()
            if ('\n' in commentStatement.comment) {
                sb.printf(literals.comment_open())
                sb.printf(commentStatement.comment)
                sb.printf(literals.comment_close())
            } else {
                sb.printf("//%s\n", commentStatement.comment)
            }
        }
    }


    override fun visit(literal: Literal) {
        fun print(prefix: Any?, suffix: Any) =
                (if (prefix != null) "$prefix#" else "") + suffix

        sb.printf(
            when (literal) {
                is IntegerLit -> print(literal.dataType.obj?.name, literal.value.abs())
                is RealLit -> print(literal.dataType.obj?.name, literal.value.abs())
                is EnumLit -> print(literal.dataType.obj?.name, literal.value)
                is ToDLit -> {
                    val (h, m, s, ms) = literal.value
                    print(literal.dataType().name, "$h:$m:$s.$ms")
                }

                is DateLit -> {
                    val (y, m, d) = literal.value
                    print(literal.dataType().name, "$y-$m-$d")
                }

                is DateAndTimeLit -> {
                    val (y, mo, d) = literal.value.date
                    val (h, m, s, ms) = literal.value.tod
                    print(literal.dataType().name, "$y-$mo-$d-$h:$m:$s.$ms")
                }

                is StringLit -> {
                    if (literal.dataType() is IECString.WSTRING) "\"${literal.value}\""
                    else "'${literal.value}'"
                }

                is NullLit -> "null"
                is TimeLit -> {
                    print(literal.dataType().name, "${literal.value.milliseconds}ms")
                }

                is BooleanLit -> literal.value.toString().uppercase(Locale.getDefault())
                is BitLit -> {
                    print(literal.dataType.obj?.name, "2#" + literal.value.toString(2))
                }

                is UnindentifiedLit -> literal.value
            })
    }

    override fun visit(arrayinit: ArrayInitialization) {
        arrayinit.initValues.joinInto(sb, ", ", "[", "]") {
            it.accept(this)
        }
    }

    override fun visit(localScope: Scope) {
        val variables = VariableScope(localScope.variables)
        variables.groupBy { it.type }
                .forEach { (type, v) ->
                    val vars = v.toMutableList()
                    vars.sortWith(compareBy { it.name })

                    //By { a, b -> a.compareTo(b) }
                    sb.nl().printf("VAR")

                    if (VariableDeclaration.INPUT and type >= VariableDeclaration.INOUT) {
                        sb.printf("_INOUT")
                    } else {
                        when {
                            VariableDeclaration.INPUT and type != 0 -> sb.printf("_INPUT")
                            VariableDeclaration.OUTPUT and type != 0 -> sb.printf("_OUTPUT")
                            VariableDeclaration.EXTERNAL and type != 0 -> sb.printf("_EXTERNAL")
                            VariableDeclaration.GLOBAL and type != 0 -> sb.printf("_GLOBAL")
                            VariableDeclaration.TEMP and type != 0 -> sb.printf("_TEMP")
                        }
                    }
                    sb.printf(" ")
                    if (VariableDeclaration.CONSTANT and type != 0)
                        sb.printf("CONSTANT ")
                    if (VariableDeclaration.RETAIN and type != 0)
                        sb.printf("RETAIN ")
                    sb.printf(" ")
                    //sb.printf(type)FUNCTION_BLOCK Crane
                    //
                    //    VAR_INPUT
                    //        CraneDown : BOOL := FALSE;
                    //        CraneOnConveyor : BOOL := FALSE;
                    //        CraneOnMagazin : BOOL := FALSE;
                    //        CraneSucked : BOOL := FALSE;
                    //        CraneUp : BOOL := FALSE;
                    //        SFCReset : BOOL := FALSE;
                    //        SliderMovedOut : BOOL := FALSE;
                    //        SliderNotMovedOut : BOOL := FALSE;
                    //        StartButtonMagazin : BOOL := FALSE;
                    //        StartVar : BOOL := FALSE;
                    //        WorkpieceReady : BOOL := FALSE;
                    //    END_VAR
                    //
                    //    VAR_OUTPUT
                    //        CraneLower : BOOL := FALSE;
                    //        CraneTurnClockwise : BOOL := FALSE;
                    //        CraneTurnCounterclockwise : BOOL := FALSE;
                    //        MagazinVacuumOff : BOOL := FALSE;
                    //        MagazinVacuumOn : BOOL := FALSE;
                    //        StartCommandCrane : BOOL := FALSE;
                    //    END_VAR
                    //
                    //    VAR
                    //        SFCInit : BOOL := FALSE;
                    //        TimeDelay_Timer : TON := (Q=FALSE, PT=USINT#0, IN=FALSE, ET=USINT#0);
                    //        TimeDelay_Timer_Duration : TIME := TIME#50.0ms;
                    //        TimeDelay_Timer_interconnect : BOOL := FALSE;
                    //        interconnectCraneStartCommand : BOOL := FALSE;
                    //    END_VAR
                    //
                    //    VAR
                    //        SFCPause : BOOL := FALSE;
                    //    END_VAR
                    //
                    //    VAR
                    //        __transit : BOOL := FALSE;
                    //        _state : STATES_CRANE := STATES_CRANE#INIT;
                    //    END_VAR
                    //
                    //
                    //    ACTION CraneTurnLeft_active
                    //        CraneTurnCounterclockwise := TRUE;
                    //        CraneTurnClockwise := FALSE;
                    //    END_ACTION
                    //    ACTION Step0_active
                    //        CraneTurnClockwise := TRUE;
                    //        CraneTurnCounterclockwise := FALSE;
                    //    END_ACTION
                    //    ACTION CraneOnConveyor_active
                    //        CraneTurnCounterclockwise := FALSE;
                    //        CraneTurnClockwise := FALSE;
                    //        CraneLower := TRUE;
                    //    END_ACTION
                    //    ACTION MagazinStop_active
                    //        CraneTurnClockwise := FALSE;
                    //        CraneTurnCounterclockwise := FALSE;
                    //        MagazinVacuumOn := TRUE;
                    //        MagazinVacuumOff := FALSE;
                    //        CraneLower := TRUE;
                    //    END_ACTION
                    //    ACTION Crane_Init_2_active
                    //        CraneLower := FALSE;
                    //    END_ACTION
                    //    ACTION Start_Crane_active
                    //        CraneLower := FALSE;
                    //        MagazinVacuumOff := TRUE;
                    //        MagazinVacuumOn := FALSE;
                    //        CraneTurnCounterclockwise := FALSE;
                    //        CraneTurnClockwise := FALSE;
                    //        StartVar := FALSE;
                    //        StartCommandCrane := FALSE;
                    //        IF (StartButtonMagazin = TRUE) THEN
                    //            interconnectCraneStartCommand := TRUE;
                    //        END_IF
                    //    END_ACTION
                    //    ACTION CraneLiftMagazine_active
                    //        CraneLower := FALSE;
                    //    END_ACTION
                    //    ACTION Interstep_active
                    //        StartCommandCrane := TRUE;
                    //    END_ACTION
                    //    ACTION release_active
                    //        MagazinVacuumOff := TRUE;
                    //        MagazinVacuumOn := FALSE;
                    //    END_ACTION
                    //    ACTION Crane_Init_active
                    //        CraneLower := TRUE;
                    //        interconnectCraneStartCommand := FALSE;
                    //    END_ACTION
                    //    ACTION TimeDelay_active
                    //        TimeDelay_Timer(IN := TRUE, PT := TimeDelay_Timer_Duration);
                    //        TimeDelay_Timer_interconnect := TimeDelay_Timer.Q;
                    //    END_ACTION
                    //    ACTION CraneLiftConveyor_active
                    //        CraneLower := FALSE;
                    //    END_ACTION
                    //    IF (SFCInit OR SFCReset) THEN
                    //        CraneDown := FALSE;
                    //        CraneLower := FALSE;
                    //        CraneOnConveyor := FALSE;
                    //        CraneOnMagazin := FALSE;
                    //        CraneSucked := FALSE;
                    //        CraneTurnClockwise := FALSE;
                    //        CraneTurnCounterclockwise := FALSE;
                    //        CraneUp := FALSE;
                    //        MagazinVacuumOff := FALSE;
                    //        MagazinVacuumOn := FALSE;
                    //        SFCInit := FALSE;
                    //        SFCReset := FALSE;
                    //        SliderMovedOut := FALSE;
                    //        SliderNotMovedOut := FALSE;
                    //        StartButtonMagazin := FALSE;
                    //        StartCommandCrane := FALSE;
                    //        StartVar := FALSE;
                    //        TimeDelay_Timer.ET := USINT#0;
                    //        TimeDelay_Timer.IN := FALSE;
                    //        TimeDelay_Timer.PT := USINT#0;
                    //        TimeDelay_Timer.Q := FALSE;
                    //        TimeDelay_Timer_Duration := TIME#50ms;
                    //        TimeDelay_Timer_interconnect := FALSE;
                    //        WorkpieceReady := FALSE;
                    //        __transit := FALSE;
                    //        _state := STATES_CRANE#INIT;
                    //        interconnectCraneStartCommand := FALSE;
                    //    END_IF
                    //    IF NOT (SFCInit OR SFCPause) THEN
                    //        //Running pipeline step: edu.kit.iti.formal.automation.st.IntroduceStateEnumVariable
                    //
                    //        //End of: edu.kit.iti.formal.automation.st.IntroduceStateEnumVariable
                    //
                    //        //Running pipeline step: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$IntroduceTransitVariable
                    //
                    //        //End of: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$IntroduceTransitVariable
                    //
                    //        //Running pipeline step: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$TheBigStateCase
                    //
                    //        CASE _state OF
                    //            STATES_CRANE#Init:
                    //                __transit := FALSE;
                    //                IF TRUE THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Start_Crane;
                    //                END_IF
                    //
                    //            STATES_CRANE#Start_Crane:
                    //                __transit := FALSE;
                    //                Start_Crane_active();
                    //                IF interconnectCraneStartCommand THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Crane_Init;
                    //                END_IF
                    //
                    //            STATES_CRANE#Crane_Init:
                    //                __transit := FALSE;
                    //                Crane_Init_active();
                    //                IF CraneDown THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Crane_Init_2;
                    //                END_IF
                    //
                    //            STATES_CRANE#Crane_Init_2:
                    //                __transit := FALSE;
                    //                Crane_Init_2_active();
                    //                IF CraneUp THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Interstep;
                    //                END_IF
                    //
                    //            STATES_CRANE#Interstep:
                    //                __transit := FALSE;
                    //                Interstep_active();
                    //                IF StartVar THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Interstep_2;
                    //                END_IF
                    //
                    //            STATES_CRANE#Interstep_2:
                    //                __transit := FALSE;
                    //                IF SliderMovedOut THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#TimeDelay;
                    //                END_IF
                    //
                    //            STATES_CRANE#TimeDelay:
                    //                __transit := FALSE;
                    //                TimeDelay_active();
                    //                IF TimeDelay_Timer_interconnect THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Turn_Right;
                    //                END_IF
                    //
                    //            STATES_CRANE#Turn_Right:
                    //                __transit := FALSE;
                    //                Step0_active();
                    //                IF CraneOnMagazin THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Interstep_Check_Workpiece;
                    //                END_IF
                    //
                    //            STATES_CRANE#Interstep_Check_Workpiece:
                    //                __transit := FALSE;
                    //                IF WorkpieceReady THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Magazin_Stop;
                    //                ELSIF NOT WorkpieceReady THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Crane_Stop;
                    //                END_IF
                    //
                    //            STATES_CRANE#Magazin_Stop:
                    //                __transit := FALSE;
                    //                MagazinStop_active();
                    //                IF CraneSucked THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Crane_Lift_Magazine;
                    //                END_IF
                    //
                    //            STATES_CRANE#Crane_Lift_Magazine:
                    //                __transit := FALSE;
                    //                CraneLiftMagazine_active();
                    //                IF CraneUp THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Crane_Turn_Left;
                    //                END_IF
                    //
                    //            STATES_CRANE#Crane_Turn_Left:
                    //                __transit := FALSE;
                    //                CraneTurnLeft_active();
                    //                IF CraneOnConveyor THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Crane_On_Conveyor;
                    //                END_IF
                    //
                    //            STATES_CRANE#Crane_On_Conveyor:
                    //                __transit := FALSE;
                    //                CraneOnConveyor_active();
                    //                IF CraneDown THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#release;
                    //                END_IF
                    //
                    //            STATES_CRANE#release:
                    //                __transit := FALSE;
                    //                release_active();
                    //                IF TRUE THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Crane_Lift_Conveyor;
                    //                END_IF
                    //
                    //            STATES_CRANE#Crane_Lift_Conveyor:
                    //                __transit := FALSE;
                    //                CraneLiftConveyor_active();
                    //                IF TRUE THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Interstep;
                    //                END_IF
                    //
                    //            STATES_CRANE#Crane_Stop:
                    //                __transit := FALSE;
                    //                IF TRUE THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_CRANE#Start_Crane;
                    //                END_IF
                    //
                    //                    END_CASE;
                    //        //End of: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$TheBigStateCase
                    //
                    //        //Running pipeline step: edu.kit.iti.formal.automation.st.SfcFlagIntroduction
                    //
                    //    END_IF
                    //    //End of: edu.kit.iti.formal.automation.st.SfcFlagIntroduction
                    //
                    //END_FUNCTION_BLOCK
                    //
                    //FUNCTION_BLOCK Magazin
                    //
                    //    VAR_INPUT
                    //        CraneDown : BOOL := FALSE;
                    //        CraneOnConveyor : BOOL := FALSE;
                    //        CraneOnMagazin : BOOL := FALSE;
                    //        CraneSucked : BOOL := FALSE;
                    //        CraneUp : BOOL := FALSE;
                    //        SFCReset : BOOL := FALSE;
                    //        SliderMovedOut : BOOL := FALSE;
                    //        SliderNotMovedOut : BOOL := FALSE;
                    //        StartButtonMagazin : BOOL := FALSE;
                    //        StartVar : BOOL := FALSE;
                    //        WorkpieceReady : BOOL := FALSE;
                    //    END_VAR
                    //
                    //    VAR_OUTPUT
                    //        MagazinGreenLamp : BOOL := FALSE;
                    //        MagazinSlider : BOOL := FALSE;
                    //        StartCommandMagazin : BOOL := FALSE;
                    //    END_VAR
                    //
                    //    VAR
                    //        SFCInit : BOOL := FALSE;
                    //        interconnectMagazineStartCommand : BOOL := FALSE;
                    //    END_VAR
                    //
                    //    VAR
                    //        SFCPause : BOOL := FALSE;
                    //    END_VAR
                    //
                    //    VAR
                    //        __transit : BOOL := FALSE;
                    //        _state : STATES_MAGAZIN := STATES_MAGAZIN#INIT;
                    //    END_VAR
                    //
                    //
                    //    ACTION Green_Lamp_active
                    //        MagazinGreenLamp := TRUE;
                    //        interconnectMagazineStartCommand := FALSE;
                    //    END_ACTION
                    //    ACTION Magazin_Init_2_active
                    //        MagazinSlider := FALSE;
                    //    END_ACTION
                    //    ACTION SliderMoveBack_active
                    //        IF ((SliderMovedOut = TRUE) AND (SliderNotMovedOut = FALSE)) THEN
                    //            MagazinSlider := FALSE;
                    //        END_IF
                    //    END_ACTION
                    //    ACTION convey_active
                    //        IF SliderNotMovedOut THEN
                    //            MagazinSlider := TRUE;
                    //        END_IF
                    //    END_ACTION
                    //    ACTION Start_Magazin_active
                    //        MagazinSlider := FALSE;
                    //        MagazinGreenLamp := FALSE;
                    //        StartVar := FALSE;
                    //        StartCommandMagazin := FALSE;
                    //        IF (StartButtonMagazin = TRUE) THEN
                    //            interconnectMagazineStartCommand := TRUE;
                    //        END_IF
                    //    END_ACTION
                    //    ACTION Magazin_Init_active
                    //        MagazinSlider := TRUE;
                    //    END_ACTION
                    //    ACTION Interstep_active
                    //        StartCommandMagazin := TRUE;
                    //    END_ACTION
                    //    IF (SFCInit OR SFCReset) THEN
                    //        CraneDown := FALSE;
                    //        CraneOnConveyor := FALSE;
                    //        CraneOnMagazin := FALSE;
                    //        CraneSucked := FALSE;
                    //        CraneUp := FALSE;
                    //        MagazinGreenLamp := FALSE;
                    //        MagazinSlider := FALSE;
                    //        SFCInit := FALSE;
                    //        SFCReset := FALSE;
                    //        SliderMovedOut := FALSE;
                    //        SliderNotMovedOut := FALSE;
                    //        StartButtonMagazin := FALSE;
                    //        StartCommandMagazin := FALSE;
                    //        StartVar := FALSE;
                    //        WorkpieceReady := FALSE;
                    //        __transit := FALSE;
                    //        _state := STATES_MAGAZIN#INIT;
                    //        interconnectMagazineStartCommand := FALSE;
                    //    END_IF
                    //    IF NOT (SFCInit OR SFCPause) THEN
                    //        //Running pipeline step: edu.kit.iti.formal.automation.st.IntroduceStateEnumVariable
                    //
                    //        //End of: edu.kit.iti.formal.automation.st.IntroduceStateEnumVariable
                    //
                    //        //Running pipeline step: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$IntroduceTransitVariable
                    //
                    //        //End of: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$IntroduceTransitVariable
                    //
                    //        //Running pipeline step: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$TheBigStateCase
                    //
                    //        CASE _state OF
                    //            STATES_MAGAZIN#Init:
                    //                __transit := FALSE;
                    //                IF TRUE THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_MAGAZIN#Start_Magazin;
                    //                END_IF
                    //
                    //            STATES_MAGAZIN#Start_Magazin:
                    //                __transit := FALSE;
                    //                Start_Magazin_active();
                    //                IF interconnectMagazineStartCommand THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_MAGAZIN#Green_Lamp;
                    //                END_IF
                    //
                    //            STATES_MAGAZIN#Green_Lamp:
                    //                __transit := FALSE;
                    //                Green_Lamp_active();
                    //                IF TRUE THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_MAGAZIN#Magazin_Init;
                    //                END_IF
                    //
                    //            STATES_MAGAZIN#Magazin_Init:
                    //                __transit := FALSE;
                    //                Magazin_Init_active();
                    //                IF TRUE THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_MAGAZIN#Magazin_Init_2;
                    //                END_IF
                    //
                    //            STATES_MAGAZIN#Magazin_Init_2:
                    //                __transit := FALSE;
                    //                Magazin_Init_2_active();
                    //                IF TRUE THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_MAGAZIN#Interstep;
                    //                END_IF
                    //
                    //            STATES_MAGAZIN#Interstep:
                    //                __transit := FALSE;
                    //                Interstep_active();
                    //                IF StartVar THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_MAGAZIN#convey;
                    //                END_IF
                    //
                    //            STATES_MAGAZIN#convey:
                    //                __transit := FALSE;
                    //                convey_active();
                    //                IF CraneOnMagazin THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_MAGAZIN#Step0;
                    //                END_IF
                    //
                    //            STATES_MAGAZIN#Step0:
                    //                __transit := FALSE;
                    //                IF CraneDown THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_MAGAZIN#Slider_Move_Back;
                    //                END_IF
                    //
                    //            STATES_MAGAZIN#Slider_Move_Back:
                    //                __transit := FALSE;
                    //                SliderMoveBack_active();
                    //                IF CraneUp THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_MAGAZIN#Step1;
                    //                END_IF
                    //
                    //            STATES_MAGAZIN#Step1:
                    //                __transit := FALSE;
                    //                IF CraneOnConveyor THEN
                    //                    __transit := TRUE;
                    //                    _state := STATES_MAGAZIN#Interstep;
                    //                END_IF
                    //
                    //                    END_CASE;
                    //        //End of: edu.kit.iti.formal.automation.st.TranslationSfcToStOld$TheBigStateCase
                    //
                    //        //Running pipeline step: edu.kit.iti.formal.automation.st.SfcFlagIntroduction
                    //
                    //    END_IF
                    //    //End of: edu.kit.iti.formal.automation.st.SfcFlagIntroduction
                    //
                    //END_FUNCTION_BLOCK
                    //
                    //PROGRAM Main
                    //    VAR
                    //        Actuator_CraneLower : BOOL := FALSE;
                    //        Actuator_CraneTurnClockwise : BOOL := FALSE;
                    //        Actuator_CraneTurnCounterclockwise : BOOL := FALSE;
                    //        Actuator_MagazinGreenLamp : BOOL := FALSE;
                    //        Actuator_MagazinSlider : BOOL := FALSE;
                    //        Actuator_MagazinVacuumOff : BOOL := FALSE;
                    //        Actuator_MagazinVacuumOn : BOOL := FALSE;
                    //        Actuator_MagazinWhiteLamp : BOOL := FALSE;
                    //        Crane : Crane := (SliderMovedOut=FALSE, SFCReset=FALSE, CraneTurnCounterclockwise=FALSE, MagazinVacuumOff=FALSE, WorkpieceReady=FALSE, CraneSucked=FALSE, MagazinVacuumOn=FALSE, interconnectCraneStartCommand=FALSE, SFCInit=FALSE, StartCommandCrane=FALSE, TimeDelay_Timer_interconnect=FALSE, TimeDelay_Timer_Duration=TIME#50.0ms, CraneOnConveyor=FALSE, CraneTurnClockwise=FALSE, CraneUp=FALSE, StartVar=FALSE, CraneLower=FALSE, SliderNotMovedOut=FALSE, StartButtonMagazin=FALSE, CraneOnMagazin=FALSE, CraneDown=FALSE, TimeDelay_Timer=(Q=FALSE, PT=USINT#0, IN=FALSE, ET=USINT#0));
                    //        Mag : Magazin := (SliderMovedOut=FALSE, MagazinGreenLamp=FALSE, SFCReset=FALSE, WorkpieceReady=FALSE, CraneSucked=FALSE, MagazinSlider=FALSE, SFCInit=FALSE, StartCommandMagazin=FALSE, CraneOnConveyor=FALSE, CraneUp=FALSE, interconnectMagazineStartCommand=FALSE, StartVar=FALSE, SliderNotMovedOut=FALSE, StartButtonMagazin=FALSE, CraneOnMagazin=FALSE, CraneDown=FALSE);
                    //        Sensor_CraneDown : BOOL := FALSE;
                    //        Sensor_CraneOnConveyor : BOOL := FALSE;
                    //        Sensor_CraneOnMagazin : BOOL := FALSE;
                    //        Sensor_CranePosition : BOOL := FALSE;
                    //        Sensor_CraneSucked : BOOL := FALSE;
                    //        Sensor_CraneUp : BOOL := FALSE;
                    //        Sensor_MagazinEmergencyStop : BOOL := FALSE;
                    //        Sensor_MagazinSwitchManuellAutomatic : BOOL := FALSE;
                    //        Sensor_SliderMovedOut : BOOL := FALSE;
                    //        Sensor_SliderNotMovedOut : BOOL := FALSE;
                    //        Sensor_StartButtonMagazin : BOOL := FALSE;
                    //        Sensor_WorkpieceReady : BOOL := FALSE;
                    //    END_VAR
                    //
                    //
                    //    Mag.SliderNotMovedOut := Sensor_SliderNotMovedOut;
                    //    Mag.SliderMovedOut := Sensor_SliderMovedOut;
                    //    Mag.CraneOnMagazin := Sensor_CraneOnMagazin;
                    //    Mag.CraneDown := Sensor_CraneDown;
                    //    Mag.CraneUp := Sensor_CraneUp;
                    //    Mag.CraneOnConveyor := Sensor_CraneOnConveyor;
                    //    Mag.WorkpieceReady := Sensor_WorkpieceReady;
                    //    Mag.StartButtonMagazin := Sensor_StartButtonMagazin;
                    //    Actuator_MagazinSlider := Mag.MagazinSlider;
                    //    Actuator_MagazinGreenLamp := Mag.MagazinGreenLamp;
                    //    Crane.WorkpieceReady := Sensor_WorkpieceReady;
                    //    Crane.CraneUp := Sensor_CraneUp;
                    //    Crane.CraneOnConveyor := Sensor_CraneOnConveyor;
                    //    Crane.CraneDown := Sensor_CraneDown;
                    //    Crane.CraneSucked := Sensor_CraneSucked;
                    //    Crane.CraneOnMagazin := Sensor_CraneOnMagazin;
                    //    Crane.SliderMovedOut := Sensor_SliderMovedOut;
                    //    Crane.StartButtonMagazin := Sensor_StartButtonMagazin;
                    //    Actuator_CraneTurnCounterclockwise := Crane.CraneTurnCounterclockwise;
                    //    Actuator_CraneTurnClockwise := Crane.CraneTurnClockwise;
                    //    Actuator_CraneLower := Crane.CraneLower;
                    //    Actuator_MagazinVacuumOff := Crane.MagazinVacuumOff;
                    //    Actuator_MagazinVacuumOn := Crane.MagazinVacuumOn;
                    //    IF Sensor_MagazinEmergencyStop THEN
                    //        Mag();
                    //        Crane();
                    //        IF Actuator_MagazinGreenLamp THEN
                    //            IF (Crane.StartCommandCrane AND Mag.StartCommandMagazin) THEN
                    //                Crane.StartVar := TRUE;
                    //                Mag.StartVar := TRUE;
                    //            END_IF
                    //        END_IF
                    //        Crane.SFCReset := FALSE;
                    //        Mag.SFCReset := FALSE;
                    //    ELSIF NOT Sensor_MagazinEmergencyStop THEN
                    //        Actuator_MagazinSlider := FALSE;
                    //        Actuator_CraneLower := FALSE;
                    //        Actuator_MagazinVacuumOn := FALSE;
                    //        Actuator_MagazinVacuumOff := TRUE;
                    //        Actuator_MagazinGreenLamp := FALSE;
                    //        Actuator_CraneTurnCounterclockwise := FALSE;
                    //        Actuator_CraneTurnClockwise := FALSE;
                    //        Crane.SFCReset := TRUE;
                    //        Mag.SFCReset := TRUE;
                    //        Crane.StartVar := FALSE;
                    //        Mag.StartVar := FALSE;
                    //    END_IF
                    //END_PROGRAM
                    //FUNCTION_BLOCK CTD
                    //
                    //    VAR_INPUT
                    //        CD : BOOL := FALSE;
                    //        LD : BOOL := FALSE;
                    //        PV : INT := INT#0;
                    //    END_VAR
                    //
                    //    VAR_OUTPUT
                    //        CV : INT := INT#0;
                    //        Q : BOOL := FALSE;
                    //    END_VAR
                    //
                    //
                    //    IF LD THEN
                    //        CV := PV;
                    //    ELSIF (CU AND (CV > INT#0)) THEN
                    //        CV := (CV - INT#1);
                    //    END_IF
                    //    Q := (CV <= INT#0);
                    //END_FUNCTION_BLOCK
                    //
                    //FUNCTION_BLOCK CTU
                    //
                    //    VAR_INPUT
                    //        CU : BOOL := FALSE;
                    //        PV : INT := INT#0;
                    //        R : BOOL := FALSE;
                    //    END_VAR
                    //
                    //    VAR_OUTPUT
                    //        CV : INT := INT#0;
                    //        Q : BOOL := FALSE;
                    //    END_VAR
                    //
                    //
                    //    IF R THEN
                    //        CV := INT#0;
                    //    ELSIF (CU AND (CV < PV)) THEN
                    //        CV := (CV + INT#1);
                    //    END_IF
                    //    Q := (CV >= PV);
                    //END_FUNCTION_BLOCK
                    //
                    //FUNCTION_BLOCK R_TRIG
                    //
                    //    VAR_INPUT
                    //        CLK : BOOL := FALSE;
                    //    END_VAR
                    //
                    //    VAR
                    //        M : BOOL := FALSE;
                    //    END_VAR
                    //
                    //    VAR_OUTPUT
                    //        Q : BOOL := FALSE;
                    //    END_VAR
                    //
                    //
                    //    Q := (CLK AND NOT M);
                    //    M := CLK;
                    //END_FUNCTION_BLOCK
                    //
                    //FUNCTION_BLOCK F_TRIG
                    //
                    //    VAR_INPUT
                    //        CLK : BOOL := FALSE;
                    //    END_VAR
                    //
                    //    VAR
                    //        M : BOOL := TRUE;
                    //    END_VAR
                    //
                    //    VAR_OUTPUT
                    //        Q : BOOL := FALSE;
                    //    END_VAR
                    //
                    //
                    //    Q := (NOT CLK AND NOT M);
                    //    M := NOT CLK;
                    //END_FUNCTION_BLOCK
                    //
                    //FUNCTION SEL : ANY
                    //
                    //    VAR_INPUT
                    //        G : BOOL := FALSE;
                    //        a : ANY;
                    //        b : ANY;
                    //    END_VAR
                    //
                    //    VAR_OUTPUT
                    //        SEL : ANY;
                    //    END_VAR
                    //
                    //    IF G THEN
                    //        SEL := a;
                    //    ELSE
                    //        SEL := b;
                    //    END_IF
                    //END_FUNCTION
                    //
                    //FUNCTION MAX : ANY_INT
                    //
                    //    VAR_OUTPUT
                    //        MAX : ANY_INT;
                    //    END_VAR
                    //
                    //    VAR_INPUT
                    //        in0 : ANY_INT;
                    //        in1 : ANY_INT;
                    //    END_VAR
                    //
                    //    MAX := sel((in0 >= in1), in0, in1);
                    //END_FUNCTION
                    //
                    //FUNCTION MIN : ANY_INT
                    //
                    //    VAR_OUTPUT
                    //        MIN : ANY_INT;
                    //    END_VAR
                    //
                    //    VAR_INPUT
                    //        in0 : ANY_INT;
                    //        in1 : ANY_INT;
                    //    END_VAR
                    //
                    //    MIN := sel((in0 <= in1), in0, in1);
                    //END_FUNCTION
                    //
                    //FUNCTION LIMIT : INT
                    //
                    //    VAR_OUTPUT
                    //        LIMIT : INT := INT#0;
                    //    END_VAR
                    //
                    //    VAR_INPUT
                    //        in : ANY_INT;
                    //        max : ANY_INT;
                    //        min : ANY_INT;
                    //    END_VAR
                    //
                    //    LIMIT := MAX(min, MIN(in, max));
                    //END_FUNCTION
                    //
                    //FUNCTION ERROR : ANY
                    //
                    //    VAR_OUTPUT
                    //        ERROR : ANY;
                    //    END_VAR
                    //
                    //    VAR
                    //        msg : STRING := WSTRING#"";
                    //    END_VAR
                    //
                    //END_FUNCTION
                    //
                    //FUNCTION SMV : ANY
                    //
                    //    VAR_OUTPUT
                    //        SMV : ANY;
                    //    END_VAR
                    //
                    //    VAR_INPUT
                    //        code : STRING := WSTRING#"";
                    //    END_VAR
                    //
                    //END_FUNCTION
                    //
                    //FUNCTION_BLOCK TON
                    //
                    //    VAR_OUTPUT
                    //        ET : USINT := USINT#0;
                    //        Q : BOOL := FALSE;
                    //    END_VAR
                    //
                    //    VAR_INPUT
                    //        IN : BOOL := FALSE;
                    //        PT : USINT := USINT#0;
                    //    END_VAR
                    //
                    //
                    //    IF IN THEN
                    //        Q := (ET = USINT#0);
                    //        IF (ET > USINT#0) THEN
                    //            ET := (ET - USINT#1);
                    //        ELSE
                    //            ET := USINT#0;
                    //        END_IF
                    //    ELSE
                    //        Q := FALSE;
                    //        ET := PT;
                    //    END_IF
                    //END_FUNCTION_BLOCK
                    //
                    //TYPE SFC_STEPS: STRUCT
                    //
                    //        T :TIME
                    //        X :BOOL
                    //        _T :TIME
                    //        _X :BOOLEND_STRUCT;
                    //
                    //END_TYPE
                    //
                    //TYPE
                    //    STATES_CRANE : (Init, Start_Crane, Crane_Init, Crane_Init_2, Interstep, Interstep_2, TimeDelay, Turn_Right, Interstep_Check_Workpiece, Magazin_Stop, Crane_Lift_Magazine, Crane_Turn_Left, Crane_On_Conveyor, release, Crane_Lift_Conveyor, Crane_Stop);
                    //    STATES_MAGAZIN : (Init, Start_Magazin, Green_Lamp, Magazin_Init, Magazin_Init_2, Interstep, convey, Step0, Slider_Move_Back, Step1);
                    //END_TYPE

                    sb.increaseIndent()
                    for (vd in vars) {
                        print(vd)
                    }
                    sb.decreaseIndent().nl().printf("END_VAR")
                    sb.nl()
                }
    }

    open fun print(vd: VariableDeclaration) {
        sb.nl()
        sb.printf(vd.name).printf(" : ")
        variableDataType(vd)
        when {
            vd.initValue != null -> {
                sb.printf(" := ")
                val (dt, v) = vd.initValue as Value<*, *>
                sb.printf(dt.repr(v))
            }
            vd.init != null -> {
                sb.printf(" := ")
                vd.init!!.accept(this)
            }
        }
        sb.printf(";")
    }

    override fun visit(structureInitialization: StructureInitialization) {
        structureInitialization.initValues.joinInto(sb, ", ", "(", ")")
        { t, v ->
            sb.printf(t).printf(" := ")
            v.accept(this)
        }
    }

    override fun visit(sfcStep: SFCStep) {
        sb.nl().printf(if (sfcStep.isInitial) "INITIAL_STEP " else "STEP ")
        sb.printf(sfcStep.name).printf(":").increaseIndent()
        sfcStep.events.forEach { aa -> visit(aa) }
        sb.decreaseIndent().nl()
        sb.printf("END_STEP").nl()

    }

    private fun visit(aa: SFCStep.AssociatedAction) {
        sb.nl().printf(aa.actionName).append('(').append(aa.qualifier!!.qualifier.symbol)
        if (aa.qualifier!!.qualifier.hasTime) {
            sb.printf(", ")
            aa.qualifier!!.time.accept(this)
        }
        sb.printf(");")
    }

    override fun visit(sfcNetwork: SFCNetwork) {
        val seq = ArrayList(sfcNetwork.steps)
        seq.sortWith(compareBy(SFCStep::isInitial).thenBy(SFCStep::name))
        seq.forEach { a -> a.accept(this) }
        sfcNetwork.steps.stream()
                .flatMap { s -> s.incoming.stream() }
                .forEachOrdered { t -> t.accept(this) }

    }

    override fun visit(sfc: SFCImplementation) {
        //sfc.actions.forEach { a -> a.accept(this) }
        sfc.networks.forEach { n -> n.accept(this) }
    }

    override fun visit(transition: SFCTransition) {
        val f = transition.from.map { it.name }.reduce { a, b -> "$a, $b" }
        val t = transition.to.map { it.name }.reduce { a, b -> "$a, $b" }

        sb.nl().printf("TRANSITION FROM ")

        if (transition.from.size > 1) {
            sb.append('(').append(f).append(')')
        } else {
            sb.printf(f)
        }
        sb.printf(" TO ")
        if (transition.to.size > 1) {
            sb.append('(').append(t).append(')')
        } else {
            sb.printf(t)
        }
        sb.printf(" := ")

        transition.guard.accept(this)
        sb.printf(";").printf(" END_TRANSITION")

    }

    private fun printBody(a: HasBody) {
        val stBody = a.stBody
        val sfcBody = a.sfcBody
        val ilBody = a.ilBody

        loop@ for (type in bodyPrintingOrder) {
            when (type) {
                BodyPrinting.ST -> stBody?.accept(this) ?: continue@loop
                BodyPrinting.SFC -> sfcBody?.accept(this) ?: continue@loop
                BodyPrinting.IL -> ilBody?.accept(IlPrinter(sb)) ?: continue@loop
            }
            break@loop
        }
    }

    /**
     *
     * clear.
     */
    fun clear() {
        sb = CodeWriter()
    }

    enum class BodyPrinting {
        ST, SFC, IL
    }

    open class StringLiterals {
        open fun operator(operator: Operator?): String {
            return operator!!.symbol
        }

        fun assign(): String {
            return " := "
        }

        fun assignmentAttempt(): String {
            return " ?= "
        }

        fun statement_separator(): String {
            return ";"
        }

        fun exit(): String {
            return "EXIT"
        }

        open fun operator(operator: UnaryOperator): String? {
            return operator.symbol
        }

        fun comment_close(): String {
            return " *)"
        }

        fun comment_open(): String {
            return "(* "
        }

        fun repr(sv: Value<*, *>): String {
            return sv.dataType.repr(sv.value)
        }

        companion object {
            fun create(): StringLiterals {
                return StringLiterals()
            }
        }
    }

    companion object {
        /**
         * Constant `SL_ST`
         */
        var SL_ST = StringLiterals.create()

        fun print(astNode: Top): String {
            val p = StructuredTextPrinter()
            astNode.accept(p)
            return p.string
        }
    }

    override fun visit(jump: JumpStatement) {
        sb.nl().write("JMP ${jump.target};")
    }

    override fun visit(label: LabelStatement) {
        sb.nl().write("${label.label}:")
    }

    override fun visit(special: SpecialStatement) {
        when (special) {
            is SpecialStatement.Assert -> {
                sb.nl().write("//# assert ")
                special.name?.let { sb.write(": $it") }
                special.exprs.joinInto(sb, separator = ", ") { it.accept(this) }
            }
            is SpecialStatement.Assume -> {
                sb.nl().write("//# assume ")
                special.name?.let { sb.write(": $it") }
                special.exprs.joinInto(sb, separator = ", ") { it.accept(this) }
            }
            is SpecialStatement.Havoc -> {
                sb.nl().write("//# havoc ")
                special.name?.let { sb.write(": $it") }
                special.variables.joinInto(sb, separator = ", ") { it.accept(this) }
            }
            else -> sb.nl().write("// special statement of type $special not supported")
        }
    }
}

