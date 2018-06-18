package edu.kit.iti.formal.automation;

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2018 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.st.StructuredTextPrinter;
import edu.kit.iti.formal.automation.st.ast.PouElements;
import edu.kit.iti.formal.smv.ast.SMVModule;
import org.junit.Test;

import java.io.File;
import java.io.IOException;

/**
 * @author Alexander Weigl
 * @version 1 (05.02.18)
 */
public class PipelineTest {
    @Test
    public void test() throws IOException {
        PouElements tle = IEC61131Facade.INSTANCE.file(new File("src/test/resources/edu/kit/iti/formal/automation/st/Crane.st"));
        IEC61131Facade.INSTANCE.resolveDataTypes(tle);
        tle = SymbExFacade.INSTANCE.simplify(tle);

        StructuredTextPrinter printer = new StructuredTextPrinter();
        tle.accept(printer);
        String s = printer.getString();
        System.out.println(s);
        SMVModule mod = SymbExFacade.INSTANCE.evaluateProgram(tle);
        System.out.println(mod);
    }
}
