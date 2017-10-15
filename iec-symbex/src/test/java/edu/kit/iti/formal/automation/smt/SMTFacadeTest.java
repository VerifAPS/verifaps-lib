package edu.kit.iti.formal.automation.smt;

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.SymbExFacade;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.smv.ast.SMVModule;
import org.antlr.v4.runtime.CharStreams;
import org.junit.Assume;
import org.junit.Test;

import java.io.IOException;
import java.io.InputStream;

/**
 * @author Alexander Weigl
 * @version 1 (16.10.17)
 */
public class SMTFacadeTest {
    @Test
    public void testTranslateTrafficLights() throws IOException {
        InputStream is = getClass().getResourceAsStream(
                "traffic_light_bools.st");
        Assume.assumeNotNull(is);
        TopLevelElements code = IEC61131Facade.file(CharStreams.fromStream(is));
        TopLevelElements symplifiedCode = SymbExFacade.simplify(code);
        SMVModule module = SymbExFacade.evaluateProgram(symplifiedCode);
        SMTProgram program = SMTFacade.translate(module);
        System.out.println(program);
    }
}