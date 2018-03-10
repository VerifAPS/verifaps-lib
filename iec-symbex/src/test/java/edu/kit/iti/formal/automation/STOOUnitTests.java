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

import com.google.common.base.CaseFormat;
import edu.kit.iti.formal.automation.scope.EffectiveSubtypeScope;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.stoo.STOOSimplifier;
import edu.kit.iti.formal.automation.stoo.trans.STOOTransformation;
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
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Augusto Modanese
 */
@RunWith(Parameterized.class)
public class STOOUnitTests {
    private static final String RESOURCES_PATH = "edu/kit/iti/formal/automation/st/stoo/unit";

    public static File[] getSTFiles(String folder) {
        URL f = STOOUnitTests.class.getClassLoader().getResource(folder);
        if (f == null) {
            System.err.format("Could not find %s%n", folder);
            return new File[0];
        }
        File file = new File(f.getFile());
        return Arrays.stream(file.listFiles()).filter(s -> !s.getName().contains(".stoo")).toArray(File[]::new);
    }

    public static STOOSimplifier.State processSTFile(File f) throws IOException {
        TopLevelElements topLevelElements =  IEC61131Facade.file(f);
        GlobalScope globalScope = IEC61131Facade.resolveDataTypes(topLevelElements);
        TopLevelElement program = topLevelElements.stream()
                .filter(tle -> tle instanceof ProgramDeclaration)
                .findAny().get();
        InstanceScope instanceScope = IEC61131Facade.findInstances(program, globalScope);
        EffectiveSubtypeScope effectiveSubtypeScope =
            IEC61131Facade.findEffectiveSubtypes(topLevelElements, globalScope, instanceScope);
        return new STOOSimplifier.State(program, topLevelElements, globalScope, instanceScope, effectiveSubtypeScope);
    }

    private static STOOSimplifier.State processSTFile(Path path) throws IOException {
        return processSTFile(path.toFile());
    }

    @Parameterized.Parameter
    public Class<? extends STOOTransformation> stooTransformation;

    @Parameterized.Parameters
    public static List<Object[]> stooTransformations() {
        return STOOSimplifier.TRANSFORMATIONS.stream()
                .flatMap(t -> Arrays.stream(getSTFiles(RESOURCES_PATH + "/"
                        + CaseFormat.UPPER_CAMEL.to(CaseFormat.LOWER_UNDERSCORE, t.getSimpleName())))
                        .map(f -> new Object[] {t, f}))
                .collect(Collectors.toList());
    }

    @Parameterized.Parameter(1)
    public File file;

    @Test
    public void testSTOOTransformation() throws IOException, IllegalAccessException, InstantiationException {
        STOOTransformation uut = stooTransformation.newInstance();

        System.out.println(uut.getClass().getSimpleName());
        System.out.println(file.getName());

        STOOSimplifier.State st = processSTFile(file);
        TopLevelElements st1Expected = processSTFile(Paths.get(file.toPath() + "oo")).getTopLevelElements();

        uut.transform(st);
        TopLevelElements st1Actual = st.getTopLevelElements();

        Collections.sort(st1Actual);
        Collections.sort(st1Expected);

        Assert.assertEquals(IEC61131Facade.print(st1Expected), IEC61131Facade.print(st1Actual));
    }
}
