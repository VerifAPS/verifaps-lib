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
import edu.kit.iti.formal.automation.st.ast.HasFbBody
import edu.kit.iti.formal.automation.st.ast.HasStBody
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope
import edu.kit.iti.formal.util.CodeWriter

/**
 *
 * @author Alexander Weigl
 * @version 1 (10.07.19)
 */
object TranslateFbdToSt : AstVisitorWithScope<Unit>() {
    override fun defaultVisit(obj: Any) {
        val st = (obj as? HasStBody)
        val body = (obj as? HasFbBody)?.fbBody
        if (st != null && body != null) {
            val out = CodeWriter()
            body.asStructuredText(out)
            st.stBody = IEC61131Facade.statements(out.stream.toString())
        }
    }
}