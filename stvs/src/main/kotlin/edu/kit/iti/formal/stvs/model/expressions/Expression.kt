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
package edu.kit.iti.formal.stvs.model.expressions

import edu.kit.iti.formal.stvs.model.common.IoVariable
import edu.kit.iti.formal.stvs.model.table.StringReadable
import javafx.beans.property.SimpleStringProperty

/**
 *
 * The abstract super class for all Expressions.
 *
 *
 * This type does not contain all information the source expression string had. That means you
 * can't get back the expression string from this Expression. For example an expression <tt>= 3</tt>
 * in a column for [IoVariable] <tt>X</tt> is parsed as <tt>X = 3</tt> by the
 * [ExpressionParser].
 *
 *
 * The only ability all Expressions currently share is getting visited.
 *
 * @author Philipp
 */
abstract class Expression : StringReadable {
    /**
     *
     * Find out what subclass of Expression this is by supplying a visitor.
     *
     * @param visitor an [ExpressionVisitor] for handling different cases of Expression
     * sublcasses
     * @param <R> the return type that the expression visitor produces
     * @return the return value that the expression visitor produced
     </R> */
    abstract fun <R> accept(visitor: ExpressionVisitor<R>): R

    override val stringRepresentationProperty = SimpleStringProperty()
}