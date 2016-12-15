package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.smv.ast.SLiteral;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SMVModule;
import org.apache.commons.io.IOUtils;
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
        List<TopLevelElement> toplevels = IEC61131Facade.file(IOUtils.toString(resource, "utf-8"));
        FunctionDeclaration func = (FunctionDeclaration) toplevels.get(0);
        SMVExpr state = SymbExFacade.evaluateFunction(func, SLiteral.TRUE, SLiteral.TRUE, SLiteral.FALSE);
        System.out.println(state);
        //Assert.assertEquals();
    }

    @Test
    public void testModuleBuilder() throws IOException {
        InputStream resource = getClass().
                getResourceAsStream("/edu/kit/iti/formal/automation/st/symbextest.st");
        TopLevelElements toplevels = IEC61131Facade.file(IOUtils.toString(resource, "utf-8"));
        IEC61131Facade.resolveDataTypes(toplevels);
        SMVModule module = SymbExFacade.evaluateProgram(
                (ProgramDeclaration) toplevels.get(2),
                (TypeDeclarations) toplevels.get(0));
        System.out.println(module);
        //System.out.println(state);
        //Assert.assertEquals();
    }
}
