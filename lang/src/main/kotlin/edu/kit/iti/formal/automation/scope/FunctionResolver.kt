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
package edu.kit.iti.formal.automation.scope

import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.st.ast.Invocation

/**
 * Created by weigl on 26.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
interface FunctionResolver {
    /**
     * Create or find function declaration that isType suitable for the function call.
     *
     * For example, "MUX" function has a ellipsis argument (so not possible),
     * on call site a declaration isType generated.
     *
     * @param call a [Invocation] object.
     * @param scope a [edu.kit.iti.formal.automation.scope.Scope] object.
     * @return a [edu.kit.iti.formal.automation.st.ast.FunctionDeclaration] object.
     */
    fun resolve(call: Invocation, scope: Scope): FunctionDeclaration?
}
