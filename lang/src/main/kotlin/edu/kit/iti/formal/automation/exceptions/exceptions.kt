/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 *
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.automation.exceptions

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.Invocation
import edu.kit.iti.formal.automation.st.ast.SymbolicReference
import edu.kit.iti.formal.automation.st.ast.Top
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
class VariableNotDefinedException(message: String) : IECException(message) {
    var scope: Scope? = null
    var reference: SymbolicReference? = null

    constructor(scope: Scope, reference: SymbolicReference) :
        this("Variable: $reference not defined in the given localScope $scope") {
        this.scope = scope
        this.reference = reference
    }

    constructor(scope: Scope, reference: String) :
        this("Variable: $reference not defined in the given localScope $scope") {
        this.scope = scope
    }
}

class DataTypeNotResolvedException(message: String) : IECException(message) {
    val expr: Top? = null
}

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
    vararg actual: AnyDt?,
) : IECException() {
    val actualDatatypes: Array<out AnyDt?> = actual

    override val message: String?
        get() = String.format(
            "Type(s) violated in %s %nExpected:%s %nGot:%s %n ",
            IEC61131Facade.print(expression),
            Arrays.toString(this.expectedDataTypes),
            Arrays.toString(this.actualDatatypes),
        )
}
