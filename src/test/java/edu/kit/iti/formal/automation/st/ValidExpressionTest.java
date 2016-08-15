package edu.kit.iti.formal.automation.st;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.*;

import java.io.*;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * Created by weigl on 02.08.16.
 */
public class ValidExpressionTest {
    private List<String> validExpression = new LinkedList<>();

    @Before
    public void setup() throws IOException {
        File ve = new File("src/test/resources/edu/kit/iti/formal/automation/st/expressions/").getAbsoluteFile();
        BufferedReader stream = new BufferedReader(new FileReader(new File(ve, "valid.txt")));
        String tmp = "";
        while ((tmp = stream.readLine()) != null) {
            if (tmp.startsWith("#"))
                continue;
            this.validExpression.add(tmp);
        }
    }


    @Test
    public void testValidExpression() {
        int i = 0;
        boolean b = true;
        List<Integer> lineNumbers = new ArrayList<>();

        for (int j = 0; j < validExpression.size(); j++) {
            String s = validExpression.get(j);
            if (test(s)) {
                i++;
            } else {
                b = false;
                System.out.println(s);
            }
        }
        System.out.printf("%d of %d validExpression are good%n", i, validExpression.size());
        assertTrue(b);

    }

    static boolean test(String s) {
        ANTLRInputStream stream = new ANTLRInputStream(s);
        IEC61131Lexer lexer = new IEC61131Lexer(stream);
        CommonTokenStream cts = new CommonTokenStream(lexer);
        IEC61131Parser parser = new IEC61131Parser(cts);

        try {
            parser.expression();
        } catch (Exception e) {
            e.printStackTrace();
            return false;
        }

        return parser.getNumberOfSyntaxErrors() == 0;
    }

}
