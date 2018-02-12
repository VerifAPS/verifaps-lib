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

package edu.kit.iti.formal.automation.st;

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import org.antlr.v4.runtime.ANTLRFileStream;
import org.junit.Assert;
import org.junit.Test;

import java.io.IOException;
import java.net.URL;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Test analysis of effective subtypes.
 *
 * @author Augusto Modanese
 */
public class EffectiveSubtypesTest {
    private final String testFileName = "edu/kit/iti/formal/automation/st/programs/instance_hierarchy.st";

    @Test
    public void testInstanceHierarchy() throws IOException {
        URL testFile = ProgramTest.class.getClassLoader().getResource(testFileName);
        TopLevelElements topLevelElements = IEC61131Facade.file(new ANTLRFileStream(testFile.getFile()));
        Scope globalScope = IEC61131Facade.resolveDataTypes(topLevelElements);
        // Only one program in test file
        ProgramDeclaration myProgram = globalScope.getPrograms().get(0);
        InstanceScope instanceScope = IEC61131Facade.findInstances(myProgram, globalScope);

        // Assert correct number of instances
        Assert.assertEquals(instanceScope.getInstancesOfClass("A").size(), 1);
        Assert.assertEquals(instanceScope.getInstancesOfClass("B").size(), 3);
        Assert.assertEquals(instanceScope.getInstancesOfClass("C").size(), 4);

        // Assert parent instances are correct
        // Instances of A
        InstanceScope.Instance instanceA = instanceScope.getInstancesOfClass("A").get(0);
        Assert.assertEquals(instanceA.getParent(), null);
        // Instances of B
        List<InstanceScope.Instance> instancesB = instanceScope.getInstancesOfClass("B");
        Set<InstanceScope.Instance> instancesBParents = new HashSet<>();
        instancesBParents.add(null); // MY_PROGRAM
        instancesBParents.add(instanceA); // MY_A
        Assert.assertEquals(instancesB.stream().map(b -> b.getParent()).collect(Collectors.toSet()),
                instancesBParents);
        // Instances of C
        List<InstanceScope.Instance> instancesC = instanceScope.getInstancesOfClass("C");
        Set<InstanceScope.Instance> instancesCParents = new HashSet<>(instancesB);
        instancesCParents.add(null);
        Assert.assertEquals(instancesC.stream().map(c -> c.getParent()).collect(Collectors.toSet()),
                instancesCParents);
    }
}
