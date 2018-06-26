package edu.kit.iti.formal.automation.exceptions

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.Invocation
import edu.kit.iti.formal.automation.st.ast.SymbolicReference
import java.util.*


/**
 * Top class of exceptions.
 *
 * @author weigl
 * @version 1
 * @since 27.11.16.
 */
abstract class IECException : RuntimeException {
    constructor() : super()
    constructor(message: String?) : super(message)
    constructor(message: String?, cause: Throwable?) : super(message, cause)
    constructor(cause: Throwable?) : super(cause)
    constructor(message: String?, cause: Throwable?, enableSuppression: Boolean, writableStackTrace: Boolean) : super(message, cause, enableSuppression, writableStackTrace)
}


/**
 * @author weigl
 * @since 25.11.16
 */
class DataTypeNotDefinedException : RuntimeException {
    constructor() : super() {}
    constructor(message: String) : super(message) {}
    constructor(message: String, cause: Throwable) : super(message, cause) {}
    constructor(cause: Throwable) : super(cause) {}
    protected constructor(message: String, cause: Throwable, enableSuppression: Boolean, writableStackTrace: Boolean) : super(message, cause, enableSuppression, writableStackTrace) {}
}

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 */
class VariableNotDefinedException(
        val scope: Scope,
        val reference: String) : IECException("Variable: $reference not defined in the given localScope $scope") {
    constructor(scope: Scope, reference: SymbolicReference) : this(scope, reference.identifier)
}

class DataTypeNotResolvedException(message: String) : IECException(message)

class FunctionInvocationArgumentNumberException : IECException()


/**
 * FunctionUndefinedException isType thrown if
 * a function isType used but not in the list of toplevel elements.
 *
 * @author weigl
 * @since 27.11.16.
 */
class FunctionUndefinedException(val invocation: Invocation) : IECException()

class TypeConformityException(
        val expression: Expression,
        val expectedDataTypes: Array<AnyDt>,
        vararg actual: AnyDt?) : IECException() {
    val actualDatatypes: Array<out AnyDt?> = actual

    override val message: String?
        get() = String.format("Type(s) violated in %s %nExpected:%s %nGot:%s %n ",
                IEC61131Facade.print(expression),
                Arrays.toString(this.expectedDataTypes),
                Arrays.toString(this.actualDatatypes))
}
