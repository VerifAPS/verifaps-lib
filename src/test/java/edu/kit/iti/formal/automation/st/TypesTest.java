package edu.kit.iti.formal.automation.st;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;


@RunWith(Parameterized.class)
public class TypesTest {
    @Parameterized.Parameters(name = "{0}")
    public static Iterable<Object[]> getStructuredTextFiles() throws IOException {
        File[] resources = ProgramTest.getResources("edu/kit/iti/formal/automation/st/types");
        ArrayList<Object[]> list = new ArrayList<>();
        for (File f : resources) {
            list.add(new Object[]{f.getAbsolutePath()});
        }
        return list;
    }


    @Parameter
    public String testFile;


    @Test
    public void testParser() throws IOException {
        IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRFileStream(testFile));
        IEC61131Parser parser = new IEC61131Parser(new CommonTokenStream(lexer));
        parser.data_type_declaration();
        Assert.assertEquals(0, parser.getNumberOfSyntaxErrors());
    }

}
