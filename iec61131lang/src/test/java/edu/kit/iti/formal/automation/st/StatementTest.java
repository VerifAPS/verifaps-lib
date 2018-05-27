package edu.kit.iti.formal.automation.st;

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

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.ast.StatementList;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;


@RunWith(Parameterized.class)
public class StatementTest {
    @Parameterized.Parameters(name = "{0}")
    public static Iterable<Object[]> getStructuredTextFiles() throws IOException {
        File[] resources = ProgramTest.getResources("edu/kit/iti/formal/automation/st/statements");
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
        IEC61131Parser parser = IEC61131Facade.INSTANCE.getParser(CharStreams.fromFileName(testFile));
        IEC61131Parser.Statement_listContext ctx = parser.statement_list();
        Assert.assertEquals(0, parser.getNumberOfSyntaxErrors());
      }

      @Test public void testCopy() throws IOException {
          StatementList sl = IEC61131Facade.INSTANCE.statements(CharStreams.fromFileName(testFile));
          Assert.assertEquals(sl, sl.clone());
      }
}
