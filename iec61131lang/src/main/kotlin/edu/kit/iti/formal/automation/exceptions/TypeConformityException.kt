package edu.kit.iti.formal.automation.exceptions

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.datatypes.AnyDt
import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.BinaryExpression
import edu.kit.iti.formal.automation.st.ast.Expression
import edu.kit.iti.formal.automation.st.ast.UnaryExpression

import java.util.Arrays

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
class TypeConformityException
/**
 *
 * Constructor for TypeConformityException.
 *
 * @param expr     a [edu.kit.iti.formal.automation.st.ast.Expression] object.
 * @param expected an array of [edu.kit.iti.formal.automation.datatypes.AnyDt] objects.
 * @param actual   a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
 */
(
        /**
         *
         * Getter for the field `expression`.
         *
         * @return a [edu.kit.iti.formal.automation.st.ast.Expression] object.
         */
        val expression: Expression,
        /**
         *
         * getExpectedDataTypes.
         *
         * @return an array of [edu.kit.iti.formal.automation.datatypes.AnyDt] objects.
         */
        val expectedDataTypes: Array<AnyDt>, vararg actual: AnyDt) : IECException() {
    /**
     *
     * getActualDatatypes.
     *
     * @return an array of [edu.kit.iti.formal.automation.datatypes.AnyDt] objects.
     */
    val actualDatatypes: Array<AnyDt>

    init {
        this.actualDatatypes = actual
    }

    /**
     * {@inheritDoc}
     */
    override fun getMessage(): String {
        return String.format("Type(s) violated in %s %nExpected:%s %nGot:%s %n ",
                IEC61131Facade.print(expression),
                Arrays.toString(this.expectedDataTypes),
                Arrays.toString(this.actualDatatypes))
    }
}
