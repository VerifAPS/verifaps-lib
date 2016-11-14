package edu.kit.iti.formal.automation.st;

import edu.kit.iti.formal.automation.TestUtils;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Created by weigl on 02.08.16.
 */
@RunWith(Parameterized.class)
public class InValidExpressionTest {
    @Parameterized.Parameters(name = "{0}")
    public static Iterable<Object[]> setup() throws IOException {
        return TestUtils.loadLines("/edu/kit/iti/formal/automation/st/expressions/invalid.txt");
    }

    @Parameterized.Parameter
    public String invalid = "";

    @Test
    public void testInValidExpression() {
        assertFalse(ValidExpressionTest.test(invalid));
    }
}

