package edu.kit.iti.formal.automation.testtables.io.xmv;



import edu.kit.iti.formal.automation.testtables.io.Report;
import edu.kit.iti.formal.automation.testtables.model.VerificationTechnique;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;

import java.io.File;

/**
 * @author Alexander Weigl
 * @version 1 (13.12.16)
 */
public class NuXmvTest {
    @Test public void simpleSuccessRun() {
        NuXMVProcess p = new NuXMVProcess()
                .commands(VerificationTechnique.IC3.getCommands())
                .moduleFile(new File("src/test/resources/success.smv").getAbsoluteFile())
                .workingDirectory(new File("target/test"))
                .output("success.log");

        Assume.assumeTrue(p.executablePath().startsWith("/"));

        p.run();
        Report.close();
        Assert.assertTrue(p.isVerified());
    }

    @Test public void simpleSuccessCE() {
        NuXMVProcess p = new NuXMVProcess()
                .commands(VerificationTechnique.IC3.getCommands())
                .moduleFile(new File("src/test/resources/counterexample.smv").getAbsoluteFile())
                .workingDirectory(new File("target/test").getAbsoluteFile())
                .output("error.log");
        Assume.assumeTrue(p.executablePath().startsWith("/"));
        p.run();
        Report.XML_MODE=true;
        Report.close();
        Assert.assertFalse(p.isVerified());
    }
}
