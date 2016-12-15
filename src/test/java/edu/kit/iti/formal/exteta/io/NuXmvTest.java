package edu.kit.iti.formal.exteta.io;


import edu.kit.iti.formal.exteta.io.NuXMVAdapter;
import org.junit.Assert;
import org.junit.Test;

import java.io.File;

/**
 * @author Alexander Weigl
 * @version 1 (13.12.16)
 */
public class NuXmvTest {
    @Test public void simpleSuccessRun() {
        NuXMVProcess p = new NuXMVProcess()
                .commands(NuXMVAdapter.IC3_COMMANDS)
                .moduleFile(new File("src/test/resources/success.smv").getAbsoluteFile())
                .workingDirectory(new File("target/test"))
                .output("success.log");
        p.run();
        Report.close();
        Assert.assertTrue(p.isVerified());
    }

    @Test public void simpleSuccessCE() {
        NuXMVProcess p = new NuXMVProcess()
                .commands(NuXMVAdapter.IC3_COMMANDS)
                .moduleFile(new File("src/test/resources/counterexample.smv").getAbsoluteFile())
                .workingDirectory(new File("target/test").getAbsoluteFile())
                .output("error.log");
        p.run();
        Report.XML_MODE=true;
        Report.close();
        Assert.assertFalse(p.isVerified());
    }
}
