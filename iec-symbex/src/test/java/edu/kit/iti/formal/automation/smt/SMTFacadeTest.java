package edu.kit.iti.formal.automation.smt;

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2017 Alexander Weigl
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
import edu.kit.iti.formal.automation.SymbExFacade;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.smv.ast.SMVModule;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Assume;
import org.junit.Test;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

/**
 * @author Alexander Weigl
 * @version 1 (16.10.17)
 */
public class SMTFacadeTest {
    @Test
    public void testTranslateTrafficLights() throws IOException {
        /*InputStream is = getClass().getResourceAsStream(
                "traffic_light_bools.st");*/
        InputStream is = new FileInputStream("src/test/resources/traffic_light_bools.st");
        Assume.assumeNotNull(is);
        TopLevelElements code = IEC61131Facade.INSTANCE.file(CharStreams.fromStream(is));
        IEC61131Facade.INSTANCE.resolveDataTypes(code);
        TopLevelElements symplifiedCode = SymbExFacade.simplify(code);
        SMVModule module = SymbExFacade.evaluateProgram(symplifiedCode);
        SMTProgram program = SMTFacade.translate(module);
        System.out.println(program.getPreamble());
        System.out.println(program.getStepDefinition(true, "_0"));
        System.out.println(program.getStepDefinition(false, "_1"));
        System.out.println(program.getAssertInit("_0"));
        System.out.println(program.getAssertNext("_0", "_1"));
    }
}
