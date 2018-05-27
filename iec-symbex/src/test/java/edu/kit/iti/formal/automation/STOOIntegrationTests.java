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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.oo.OOIEC61131Facade;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.scope.EffectiveSubtypeScope;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.stoo.STOOSimplifier;
import edu.kit.iti.formal.automation.visitors.Utils;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.Objects;

/**
 * @author Augusto Modanese
 */
@RunWith(Parameterized.class)
public class STOOIntegrationTests {
    private static final String RESOURCES_PATH = "edu/kit/iti/formal/automation/st/stoo/integration";

    @Parameterized.Parameter
    public File file;

    private static File[] getSTFiles() {
        URL f = STOOIntegrationTests.class.getClassLoader().getResource(STOOIntegrationTests.RESOURCES_PATH);
        if (f == null) {
            System.err.format("Could not find %s%n", STOOIntegrationTests.RESOURCES_PATH);
            return new File[0];
        }
        File file = new File(f.getFile());
        return Arrays.stream(Objects.requireNonNull(file.listFiles()))
                .filter(s -> !s.getName().contains(".stoo")).toArray(File[]::new);
    }

    private static STOOSimplifier.State processSTFile(File f) throws IOException {
        TopLevelElements topLevelElements =  IEC61131Facade.INSTANCE.file(f);
        Scope globalScope = IEC61131Facade.INSTANCE.resolveDataTypes(topLevelElements);
        TopLevelElement program = Utils.INSTANCE.findProgram(topLevelElements);
        assert program != null;
        InstanceScope instanceScope = OOIEC61131Facade.INSTANCE.findInstances(program, globalScope);
        EffectiveSubtypeScope effectiveSubtypeScope =
                OOIEC61131Facade.INSTANCE.findEffectiveSubtypes(topLevelElements, globalScope, instanceScope);
        return new STOOSimplifier.State(program, topLevelElements, globalScope, instanceScope, effectiveSubtypeScope);
    }

    private static STOOSimplifier.State processSTFile(Path path) throws IOException {
        return processSTFile(path.toFile());
    }

    @Parameterized.Parameters
    public static Object[] files() {
        return getSTFiles();
    }

    @Test(timeout = 4000)
    public void testSTOOTransformation() throws IOException {
        System.out.println(file.getName());

        STOOSimplifier.State st = processSTFile(file);
        TopLevelElements st1Expected = processSTFile(Paths.get(file.toPath() + "oo")).getTopLevelElements();

        STOOSimplifier simplifier = new STOOSimplifier(st);
        simplifier.simplify();
        TopLevelElements st1Actual = st.getTopLevelElements();

        Collections.sort(st1Actual);
        Collections.sort(st1Expected);

        Assert.assertEquals(IEC61131Facade.INSTANCE.print(st1Expected), IEC61131Facade.INSTANCE.print(st1Actual));
    }
}
