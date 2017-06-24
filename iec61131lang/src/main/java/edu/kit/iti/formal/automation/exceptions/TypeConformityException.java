package edu.kit.iti.formal.automation.exceptions;

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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;
import edu.kit.iti.formal.automation.st.ast.BinaryExpression;
import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.st.ast.UnaryExpression;

import java.util.Arrays;

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class TypeConformityException extends IECException {
    private final Any[] actual, expected;
    private final Expression expression;

    /**
     * <p>Constructor for TypeConformityException.</p>
     *
     * @param expr     a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     * @param expected an array of {@link edu.kit.iti.formal.automation.datatypes.Any} objects.
     * @param actual   a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public TypeConformityException(Expression expr, Any[] expected, Any... actual) {
        this.expression = expr;
        this.expected = expected;
        this.actual = actual;
    }

    /**
     * <p>getActualDatatypes.</p>
     *
     * @return an array of {@link edu.kit.iti.formal.automation.datatypes.Any} objects.
     */
    public Any[] getActualDatatypes() {
        return actual;
    }

    /**
     * <p>getExpectedDataTypes.</p>
     *
     * @return an array of {@link edu.kit.iti.formal.automation.datatypes.Any} objects.
     */
    public Any[] getExpectedDataTypes() {
        return expected;
    }

    /**
     * <p>Getter for the field <code>expression</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public Expression getExpression() {
        return expression;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getMessage() {
        return String.format("Type(s) violated in %s %nExpected:%s %nGot:%s %n ",
                IEC61131Facade.print(expression),
                Arrays.toString(this.expected),
                Arrays.toString(this.actual));
    }
}
