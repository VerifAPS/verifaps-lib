/**
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
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
 */
package edu.kit.iti.formal.automation.testtables.io;


import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.schema.DataType;
import edu.kit.iti.formal.automation.testtables.schema.IoVariable;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SVariable;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by weigl on 15.12.16.
 */
@RunWith(Parameterized.class)
public class CellExpressionTest {
    private final GeneralizedTestTable gtt;
    String expr;

    public CellExpressionTest(String expr) {
        this.expr = expr;
        this.gtt = defaultTestTable();
    }

    static GeneralizedTestTable defaultTestTable() {
        GeneralizedTestTable gtt = new GeneralizedTestTable();
        gtt.add(iovar("a", "input"));
        gtt.add(iovar("b", "input"));
        gtt.add(iovar("c", "input"));
        gtt.add(iovar("d", "input"));
        return gtt;
    }

    private static IoVariable iovar(String name, String io) {
        IoVariable i = new IoVariable();
        i.setIo(io);
        i.setName(name);
        i.setDataType(DataType.INT);
        return i;
    }

    public static final String[] CASES = new String[]{
            ">2", "<52152343243214234", "!=6", "<>-16134",
            "-243261", "a", "a+b", "(a)+(((b+c)+d))/2",
            "convert(a,2)", "TRUE", "true", "false", "FALSE",
            "a[-5]", "[2+2, 6]", "[-61+2, -61]"
    };

    @Parameterized.Parameters(name = "{0}")
    public static List<Object[]> genTests() {
        return Arrays.stream(CASES)
                .map(s -> new Object[]{s})
                .collect(Collectors.toList());
    }

    @Test
    public void parse() {
        SVariable v = SVariable.create("Q").withSigned(16);
        SMVExpr e = IOFacade.parseCellExpression(expr, v, gtt);
        System.out.println(e);
    }


}
