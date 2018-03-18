/*
 * #%L
 * iec61131lang
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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.smv.ast.SMVModule;
import edu.kit.iti.formal.smv.ast.SMVType;
import edu.kit.iti.formal.smv.ast.SVariable;
import org.jetbrains.annotations.NotNull;
import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;

/**
 * @author Augusto Modanese
 */
@RunWith(Parameterized.class)
public class FacadeSTFileTest {
    private static final String RESOURCES_PATH = "edu/kit/iti/formal/automation/smv";

    private Process nuxmv;

    public static File[] getSTFiles(String folder) {
        URL f = STOOIntegrationTests.class.getClassLoader().getResource(folder);
        if (f == null) {
            System.err.format("Could not find %s%n", folder);
            return new File[0];
        }
        File file = new File(f.getFile());
        return Arrays.stream(file.listFiles()).filter(s -> s.getName().contains(".st")).toArray(File[]::new);
    }

    @Parameterized.Parameters
    public static Object[] files() {
        return getSTFiles(RESOURCES_PATH);
    }

    @Parameterized.Parameter
    public File file;

    private Path getSMVFile() {
        return Paths.get(getSMVDirectory() + "/" + file.getName() + ".smv");
    }

    private Path getSMVDirectory() {
        return Paths.get(file.getParent() + "/gen/");
    }

    @Before
    public void setUp() throws IOException {
        if (!Files.exists(getSMVDirectory()))
            Files.createDirectory(getSMVDirectory());
    }

    @Test(timeout = 4000)
    public void testSMVEvaluateProgram() throws IOException, InterruptedException {
        System.out.println(file.getName());
        TopLevelElements code = IEC61131Facade.file(file);
        SMVModule module = SymbExFacade.evaluateProgram(code);
        SMVModule mainModule = createMainModule(module);
        StringBuilder smvCode = new StringBuilder(mainModule.toString());
        smvCode.append(module.toString());
//      System.out.println(smvCode);
        PrintWriter printWriter = new PrintWriter(getSMVFile().toString());
        printWriter.println(smvCode);
        printWriter.close();
        ProcessBuilder processBuilder = new ProcessBuilder();
        processBuilder.redirectOutput(ProcessBuilder.Redirect.INHERIT);
        processBuilder.redirectError(ProcessBuilder.Redirect.INHERIT);
        processBuilder.command("nuXmv", getSMVFile().toString());
        nuxmv = processBuilder.start();
        Assert.assertEquals(nuxmv.waitFor(), 0);
    }

    @After
    public void tearDown() throws IOException {
        Files.delete(getSMVFile());
        nuxmv.destroy();
    }

    private SMVModule createMainModule(@NotNull SMVModule uut) {
        SMVModule mainModule = new SMVModule();
        mainModule.setName("main");
        mainModule.setStateVars(new ArrayList<>(uut.getModuleParameters()));
        mainModule.getStateVars().add(
                new SVariable("uut", new SMVType.Module(uut.getName(), uut.getModuleParameters())));
        return mainModule;
    }
}
