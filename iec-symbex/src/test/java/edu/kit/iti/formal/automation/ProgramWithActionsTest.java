package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.st0.STSimplifier;
import org.antlr.v4.runtime.CharStreams;
import org.jetbrains.annotations.NotNull;
import org.junit.Test;

import java.io.IOException;

/**
 * @author Alexander Weigl
 * @version 1 (18.02.18)
 */
public class ProgramWithActionsTest {
    @Test
    public void test() throws IOException {
        TopLevelElements tle = IEC61131Facade.file(CharStreams.fromStream(
                getClass().getResourceAsStream("program_with_actions.st")
        ));
        TopLevelElements newTle = SymbExFacade.simplify(tle);
        System.out.println(IEC61131Facade.print(newTle));
    }
}
