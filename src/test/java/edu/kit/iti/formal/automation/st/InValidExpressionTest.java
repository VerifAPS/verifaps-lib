package edu.kit.iti.formal.automation.st;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Before;
import org.junit.Test;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import static org.junit.Assert.assertTrue;

/**
 * Created by weigl on 02.08.16.
 */
public class InValidExpressionTest {
    private List<String> inValidExpression = new LinkedList<>();

    @Before
    public void setup() throws IOException {
        File ve = new File("src/test/resources/edu/kit/iti/formal/automation/st/expressions/").getAbsoluteFile();
        BufferedReader stream = new BufferedReader(new FileReader(new File(ve, "invalid.txt")));
        String tmp = "";
        while ((tmp = stream.readLine()) != null) {
            if (tmp.startsWith("#"))
                continue;
            this.inValidExpression.add(tmp);
        }
    }


    @Test
    public void testValidExpression() {
        int i = 0;
        boolean b = true;
        List<Integer> lineNumbers = new ArrayList<>();

        for (int j = 0; j < inValidExpression.size(); j++) {
            try {
                String s = inValidExpression.get(j);
                if (ValidExpressionTest.test(s)) {
                    b = false;
                    System.out.println(s);
                } else {
                    i++;
                }
            } catch (Exception e) {
                i++;
            }
            System.out.printf("%d of %d inValidExpression are good%n", i, inValidExpression.size());
            assertTrue(b);
        }
    }
}
