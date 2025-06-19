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
package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope

/**
 * This analysis sets an `stBody` generated from an `sfcBody`.
 * @author weigl
 * @author gorenflo
 */
class TranslateSfcToSt : AstVisitorWithScope<Unit>() {
    val newTypes = TypeDeclarations()

    override fun defaultVisit(obj: Any) {}

    override fun visit(programDeclaration: ProgramDeclaration) {
        super.visit(programDeclaration)
        programDeclaration.sfcBody?.also {
            if (programDeclaration.stBody == null) {
                val (t, st) = IEC61131Facade.translateSfcToSt(programDeclaration.scope, it, programDeclaration.name)
                programDeclaration.stBody = st
                newTypes.addAll(t)
            }
        }
    }

    override fun visit(actionDeclaration: ActionDeclaration) {
        actionDeclaration.sfcBody?.also {
            if (actionDeclaration.stBody == null) {
                val (t, st) = IEC61131Facade.translateSfcToSt(scope, it, "${actionDeclaration.name}_")
                actionDeclaration.stBody = st
                newTypes.addAll(t)
            }
        }
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration) {
        super.visit(functionBlockDeclaration)
        functionBlockDeclaration.sfcBody?.also {
            if (functionBlockDeclaration.stBody == null) {
                val (t, st) = IEC61131Facade.translateSfcToSt(functionBlockDeclaration.scope, it, functionBlockDeclaration.name)
                functionBlockDeclaration.stBody = st
                newTypes.addAll(t)
            }
        }
    }
}
