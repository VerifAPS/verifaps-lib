package edu.kit.iti.formal.automation.testtables.io.xmv;

/*-
 * #%L
 * geteta
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
