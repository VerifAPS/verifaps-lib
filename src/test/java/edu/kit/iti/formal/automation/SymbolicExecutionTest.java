package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.smv.SymbolicExecutioner;
import edu.kit.iti.formal.automation.st.ast.StatementList;
import org.junit.Assert;
import org.junit.Test;

/**
 * @author Alexander Weigl
 * @version 1 (27.11.16)
 */
public class SymbolicExecutionTest {


    @Test
    public void simpleTest() {
        StatementList list = IEC61131Facade.statements(
                "a := 2;" +
                        "c := 3;" +
                        "c := a+c;" +
                        "b := 2*a+c;");
        SymbolicExecutioner se = new SymbolicExecutioner();
        list.visit(se);
        Assert.assertEquals("{a=2, b=((2*2)+(2+3)), c=(2+3)}",
                se.peek().toString()
        );
    }

    @Test
    public void simpleIfTest() {
        StatementList list = IEC61131Facade.statements(
                "a := 2; c:= 4; IF a = 2 THEN b := 2; ELSE b := 1; c:=2; END_IF;");
        SymbolicExecutioner se = new SymbolicExecutioner();
        list.visit(se);
        Assert.assertEquals("{a=if :: (2=2)->2\n" +
                        ":: true->2 fi, b=if :: (2=2)->2\n" +
                        ":: true->1 fi, c=if :: (2=2)->4\n" +
                        ":: true->2 fi}",
                se.peek().toString());
    }


}
