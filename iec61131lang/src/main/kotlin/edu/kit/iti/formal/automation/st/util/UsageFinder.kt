package edu.kit.iti.formal.automation.st.util

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.st.ast.AssignmentStatement
import edu.kit.iti.formal.automation.visitors.Visitable
import java.util.*

/**
 * Created by weigl on 10/07/14.
 *
 * @author weigl
 * @version $Id: $Id
 */
class UsageFinder : AstVisitor<Unit>() {
    override fun defaultVisit(obj: Any) {}

    var writtenReferences: MutableSet<String> = HashSet()
    var readedReference: Set<String> = HashSet()

    override fun visit(assignmentStatement: AssignmentStatement) {
        writtenReferences.add(assignmentStatement.location.toString())
        assignmentStatement.expression.accept(this)
        
    }

    /*@Override
    public Object accept(SymbolicReference symbolicReference) {
        readedReference.add(symbolicReference.getName());
        ;
    }*/

    companion object {
        /**
         *
         * investigate.
         *
         * @param visitable a [edu.kit.iti.formal.automation.visitors.Visitable] object.
         * @return a [edu.kit.iti.formal.automation.st.util.UsageFinder] object.
         */
        fun investigate(visitable: Visitable): UsageFinder {
            val waf = UsageFinder()
            visitable.accept(waf)
            return waf
        }
    }
}
