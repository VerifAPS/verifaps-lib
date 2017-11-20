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

import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.stoo.STOOSimplifier;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.Arrays;

/**
 * @author Augusto Modanese
 */
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
        return new STOOSimplifier.State(program, topLevelElements, globalScope, instanceScope);
    }
}
