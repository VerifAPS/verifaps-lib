package edu.kit.iti.formal.smv.parser;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
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


import edu.kit.iti.formal.smv.ast.SMVModule;
import edu.kit.iti.formal.smv.printers.FilePrinter;
import edu.kit.iti.formal.smv.printers.Printer;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (10.06.17)
 */
@RunWith(Parameterized.class)
public class ModuleTests {
    @Parameterized.Parameters(name = "{0}")
    public static Iterable<Object[]> getScripts() throws IOException {
        return TestHelper.getResourcesAsParameters("edu/kit/iti/formal/smv/parser/modules");
    }

    @Parameterized.Parameter
    public File f;

    @Test
    public void parse() throws IOException {
        SMVLexer l = new SMVLexer(CharStreams.fromFileName(f.getAbsolutePath()));
        l.getAllTokens().forEach(System.out::println);

        SMVParser slp = TestHelper.getParser(f);
        SMVParser.ModulesContext ctx = slp.modules();

        SMVTransformToAST a = new SMVTransformToAST();
        List<SMVModule> list = (List<SMVModule>) ctx.accept(a);
        for (SMVModule m : list) {
            Printer p = new FilePrinter(Paths.get(f.getAbsolutePath() + ".smv").toFile());
            System.out.println(m.accept(p));
        }
        Assert.assertEquals(0, slp.getNumberOfSyntaxErrors());
    }

}
