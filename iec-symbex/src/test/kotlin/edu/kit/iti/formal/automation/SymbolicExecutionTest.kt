package edu.kit.iti.formal.automation

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2016 Alexander Weigl
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

import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.smv.SymbolicExecutioner
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import org.junit.Assert
import org.junit.Before
import org.junit.Test

/**
 * @author Alexander Weigl
 * @version 1 (27.11.16)
 */
class SymbolicExecutionTest {
    private lateinit var se: SymbolicExecutioner

    @Before
    fun setupExecutioner() {
        se = SymbolicExecutioner()
        arrayOf("a", "b", "c", "d", "e", "f")
                .map { VariableDeclaration(it, 0, INT) }
                .forEach { se.lift(it) }
    }

    @Test
    fun simpleTest() {
        val list = IEC61131Facade.statements(
                "a := 2;" +
                        "c := 3;" +
                        "c := a+c;" +
                        "b := 2*a+c;")
        IEC61131Facade.resolveDataTypes(elements = list)
        list.accept(se)
        Assert.assertEquals(
                "{a=0sd16_2, b=0sd16_2 * 0sd16_2 + 0sd16_2 + 0sd16_3, c=0sd16_2 + 0sd16_3}",
                se.peek().toString()
        )
    }

    @Test
    fun simpleIfTest() {
        val list = IEC61131Facade.statements(
                "a := 2; c:= 4; b:=0; IF a = 2 THEN b := 2; ELSE b := 1; c:=2; END_IF;")
        IEC61131Facade.resolveDataTypes(elements = list)
        list.accept(se)
        Assert.assertEquals(
                "{a=0sd16_2, b=case \n" +
                        "0sd16_2 = 0sd16_2 : 0sd16_2; TRUE : 0sd16_1; \n" +
                        "esac, c=case \n" +
                        "0sd16_2 = 0sd16_2 : 0sd16_4; TRUE : 0sd16_2; \n" +
                        "esac}",
                se.peek().toString())
    }

    /*
    // Broken! and won't fix.
    @Test
    public void simpleIfWithoutElse() {
        StatementList list = IEC61131Facade.statements(
                "a := 1; c:= a; b:=b; IF a = 2 THEN b := 2; c := 1;END_IF;");

        SVariable a = SVariable.create("a").withSigned(16);
        SVariable b = SVariable.create("b").withSigned(16);
        SVariable c = SVariable.create("c").withSigned(16);

        SLiteral one = SLiteral.create(1L).asSigned(16);
        SLiteral two = SLiteral.create(2L).asSigned(16);

        SymbolicState ss = new SymbolicState();

        ss.put(a, one);
        ss.put(b, SMVFacade.caseexpr(one.equal(two), two, SLiteral.LTRUE, b));

        se.peek().put(b,b);
        list.accept(se);

        ss.forEach((key, value) -> {
            Assert.assertEquals(value, se.peek().get(key));
        });

        //Assert.assertEquals(ss, se.peek());
    }
    */
}
