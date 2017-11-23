package edu.kit.iti.formal.automation;

/*-
 * #%L
 * iec-symbex
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

import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SMVModule;
import edu.kit.iti.formal.smv.ast.SVariable;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Test;

import java.io.IOException;
import java.io.InputStream;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class FacadeTest {
    @Test
    public void testEvaluateFunction() throws IOException {
        InputStream resource = getClass().getResourceAsStream("/edu/kit/iti/formal/automation/st/func_sel.st");
        List<TopLevelElement> toplevels = IEC61131Facade.file(CharStreams.fromStream(resource));
        FunctionDeclaration func = (FunctionDeclaration) toplevels.get(0);
        SMVExpr state = SymbExFacade.evaluateFunction(func,
                SVariable.create("a").asBool(),
                SVariable.create("b").asBool(),
                SVariable.create("c").asBool());
        System.out.println(state);
        //Assert.assertEquals();
    }

    @Test
    public void testModuleBuilder() throws IOException {
        InputStream resource = getClass().
                getResourceAsStream("/edu/kit/iti/formal/automation/st/symbextest.st");
        TopLevelElements toplevels = IEC61131Facade.file(CharStreams.fromStream(resource));

        GlobalScope globalScope = IEC61131Facade.resolveDataTypes(toplevels);
        SMVModule module = SymbExFacade.evaluateProgram(
                (ProgramDeclaration) toplevels.get(2),
                (TypeDeclarations) toplevels.get(0), globalScope);
        System.out.println(module);
        //System.out.println(state);
        //Assert.assertEquals();
    }
}
