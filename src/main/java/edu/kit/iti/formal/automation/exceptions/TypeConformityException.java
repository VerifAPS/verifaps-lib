package edu.kit.iti.formal.automation.exceptions;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.st.STUtil;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;
import edu.kit.iti.formal.automation.st.ast.BinaryExpression;
import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.st.ast.UnaryExpression;

import java.util.Arrays;

/**
 * Created by weigl on 24.11.16.
 */
public class TypeConformityException extends Exception {
    private final Any[] actual, expected;
    private final Expression expression;

    public TypeConformityException(Expression expr, Any[] expected, Any... actual) {
        this.expression = expr;
        this.expected = expected;
        this.actual = actual;
    }

    public Any[] getActualDatatypes() {
        return actual;
    }

    public Any[] getExpectedDataTypes() {
        return expected;
    }

    public Expression getExpression() {
        return expression;
    }

    @Override
    public String getMessage() {
        return String.format("Type(s) violated in %s %nExpected:%s %nGot:%s %n ",
                STUtil.print(expression),
                Arrays.toString(this.expected),
                Arrays.toString(this.actual));
    }
}
