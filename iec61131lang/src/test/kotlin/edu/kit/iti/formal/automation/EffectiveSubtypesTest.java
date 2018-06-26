/*
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
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

/**
 * Test analysis of effective subtypes.
 *
 * @author Augusto Modanese
public class EffectiveSubtypesTest {
    @Test
    public void testInstanceHierarchy() throws IOException {
        String testFileName = "edu/kit/iti/formal/automation/st/programs/instance_hierarchy.st";
        URL testFile = ProgramTest.class.getClassLoader().getResource(testFileName);
        assert testFile != null;
        PouElements topLevelElements = IEC61131Facade.INSTANCE.file(new ANTLRFileStream(testFile.getFile()));
        Scope globalScope = IEC61131Facade.INSTANCE.resolveDataTypes(topLevelElements);
        ProgramDeclaration myProgram = Utils.INSTANCE.findProgram(topLevelElements);
        assert myProgram != null;
        InstanceScope instanceScope = OOIEC61131Facade.INSTANCE.findInstances(myProgram, globalScope);

        // Assert correct number of instances
        Assert.assertEquals(instanceScope.getInstancesOfClass("A").size(), 1);
        Assert.assertEquals(instanceScope.getInstancesOfClass("B").size(), 3);
        Assert.assertEquals(instanceScope.getInstancesOfClass("C").size(), 4);

        // Assert parent instances are correct
        // Instances of A
        InstanceScope.Instance instanceA = instanceScope.getInstancesOfClass("A").get(0);
        Assert.assertNull(instanceA.getParent());
        // Instances of B
        List<InstanceScope.Instance> instancesB = instanceScope.getInstancesOfClass("B");
        Set<InstanceScope.Instance> instancesBParents = new HashSet<>();
        instancesBParents.add(null); // MY_PROGRAM
        instancesBParents.add(instanceA); // MY_A
        Assert.assertEquals(instancesB.stream().map(InstanceScope.Instance::getParent).collect(Collectors.toSet()),
                instancesBParents);
        // Instances of C
        List<InstanceScope.Instance> instancesC = instanceScope.getInstancesOfClass("C");
        Set<InstanceScope.Instance> instancesCParents = new HashSet<>(instancesB);
        instancesCParents.add(null);
        Assert.assertEquals(instancesC.stream().map(InstanceScope.Instance::getParent).collect(Collectors.toSet()),
                instancesCParents);
    }
}
*/