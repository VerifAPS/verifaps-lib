/**
 * geteta
 * <p>
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * <p>
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables;

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.State;
import org.junit.Assert;
import org.junit.Test;

import javax.xml.bind.JAXBException;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
public class OmegaSimplifierTest {
    @Test
    public void run_omga_simplify1() throws Exception {
        String ignored = test("simplify1.xml");
        Assert.assertEquals("5,6,7,8", ignored);
    }


    private String test(String filename) throws JAXBException {
        GeneralizedTestTable gtt = Facade.INSTANCE.readTable("src/test/resources/omega/" + filename);
        OmegaSimplifier os = new OmegaSimplifier(gtt);
        os.run();
        return os.getIgnored().stream().map(State::getId).collect(Collectors.joining(","));
    }

    @Test
    public void run_omga_simplify2() throws Exception {
        String ignored = test("simplify2.xml");
        Assert.assertEquals("6,7,8,9", ignored);
    }

    @Test
    public void run_omga_simplify3() throws Exception {
        String ignored = test("simplify3.xml");
        Assert.assertEquals("22,23,24", ignored);
    }

}