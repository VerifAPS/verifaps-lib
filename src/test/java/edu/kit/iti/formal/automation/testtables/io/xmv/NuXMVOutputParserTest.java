package edu.kit.iti.formal.automation.testtables.io.xmv;

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.testtables.report.Counterexample;
import org.apache.commons.io.IOUtils;
import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;

import static org.junit.Assert.assertEquals;

/**
 * @author Alexander Weigl
 * @version 1 (03.01.17)
 */
public class NuXMVOutputParserTest {
    NuXMVOutputParser op;

    @Before
    public void setup() throws IOException {
        Reader res = new InputStreamReader(getClass().getResourceAsStream("/log_50.txt"));
        if (res == null) {
            String content = IOUtils.toString(res);
            op = new NuXMVOutputParser(content);
        }
    }


    @Test
    public void run() throws Exception {
        Assume.assumeTrue(op != null);
        Counterexample ce = op.run();
        assertEquals(57, ce.getStep().size());
    }

}
