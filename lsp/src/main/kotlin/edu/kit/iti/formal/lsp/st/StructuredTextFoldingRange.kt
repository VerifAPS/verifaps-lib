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
package edu.kit.iti.formal.lsp.st

import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.lsp.FoldingRangeHelper

/**
 * Folding ranges for Structured Text, registered against the generated
 * IEC 61131 parser contexts.
 */
object StructuredTextFoldingRange : FoldingRangeHelper() {
    init {
        register<IEC61131Parser.Program_declarationContext> { it.identifier.text }
        register<IEC61131Parser.Function_declarationContext> { it.identifier.text }
        register<IEC61131Parser.Function_block_declarationContext> { it.identifier.text }
        register<IEC61131Parser.Class_declarationContext> { it.identifier.text }
        register<IEC61131Parser.Interface_declarationContext> { it.identifier.text }
        register<IEC61131Parser.MethodContext> { it.identifier.text }
        register<IEC61131Parser.Var_declsContext> { "VAR" }
        register<IEC61131Parser.If_statementContext> { "IF" }
        register<IEC61131Parser.Case_statementContext> { "CASE" }
        register<IEC61131Parser.Type_declarationContext> { "TYPE" }
    }
}