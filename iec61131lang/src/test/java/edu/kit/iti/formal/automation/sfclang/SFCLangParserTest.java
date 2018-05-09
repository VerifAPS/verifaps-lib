package edu.kit.iti.formal.automation.sfclang;

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
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST;
import edu.kit.iti.formal.automation.st.PrettyPrinterTest;
import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration;
import org.antlr.v4.runtime.CharStreams;
import org.apache.commons.io.FileUtils;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collection;

/**
 * Created by weigl on 07.02.16.
 */
@RunWith(Parameterized.class)
public class SFCLangParserTest {
    private String inputFilename;
    private FunctionBlockDeclaration ctx;
    private IEC61131Parser parser;

    public SFCLangParserTest(String inputFilename) {
        this.inputFilename = inputFilename;
    }

    @Parameterized.Parameters(name = "{0}")
    public static Collection<String> data() {
        return Arrays.asList("data/Algo1_left.sfc",
                "data/Algo1_right.sfc",
                "data/Delay1_left.sfc",
                "data/Delay1_right.sfc",
                "data/EmptyStep1_left.sfc",
                "data/EmptyStep1_right.sfc",
                "data/Idempotence1_left.sfc",
                "data/Idempotence1_right.sfc",
                "data/Input1_left.sfc",
                "data/Input1_right.sfc",
                "data/LoopUnwinding1_left.sfc",
                "data/LoopUnwinding1_right.sfc",
                "data/Transition1_left.sfc",
                "data/Transition1_right.sfc",
                "data/Transition2_left.sfc",
                "data/Transition2_right.sfc",
                "data/Types1_left.sfc",
                "data/Types1_right.sfc");
    }

    @Before
    public void parse() throws IOException {
        parser = IEC61131Facade.getParser(CharStreams.fromStream(getClass().getResourceAsStream(inputFilename)));
        ctx = (FunctionBlockDeclaration) parser.function_block_declaration().accept(new IECParseTreeToAST());
    }

    @Test
    public void read() throws ClassNotFoundException, IOException {
        Assert.assertEquals(0, parser.getNumberOfSyntaxErrors());
        parser.getErrorReporter().throwException(() -> {
            try {
                return FileUtils.readFileToString(new File(inputFilename), "utf-8").split("\n");
            } catch (IOException e) {
                return new String[]{};
            }
        });
        Assert.assertFalse(parser.getErrorReporter().hasErrors());
        Assert.assertNotNull(ctx.getSfcBody());
    }

    @Test
    public void prettyPrintByString() throws IOException {
        Assume.assumeTrue(false);
        PrettyPrinterTest.testPrettyPrintByString(ctx,
                new File("src/test/resources/edu/kit/iti/formal/automation/sfclang/",inputFilename));
    }
}
