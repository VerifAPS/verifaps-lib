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

import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.smv.ast.SVariable
import org.antlr.v4.runtime.CharStreams
import org.junit.Assert
import org.junit.Assume
import org.junit.Test

import java.io.IOException

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
class FacadeTest {
    @Test
    @Throws(IOException::class)
    fun testEvaluateFunction() {
        val resource = javaClass.getResourceAsStream("/edu/kit/iti/formal/automation/st/func_sel.st")
        Assume.assumeNotNull(resource)
        val toplevels = IEC61131Facade.file(CharStreams.fromStream(resource))
        IEC61131Facade.resolveDataTypes(toplevels)
        val func = toplevels[0] as FunctionDeclaration
        val state = SymbExFacade.evaluateFunction(func,
                SVariable.create("a").asBool(),
                SVariable.create("b").asBool(),
                SVariable.create("c").asBool())
        //System.out.println(state);
        Assert.assertNotEquals(null, state)
        Assert.assertEquals(
                "case \n" +
                        "b : c; TRUE : FALSE; \n" +
                        "esac",
                state.repr())
    }

    @Test
    @Throws(IOException::class)
    fun testModuleBuilder() {
        val resource = javaClass.getResourceAsStream("/edu/kit/iti/formal/automation/st/symbextest.st")
        val toplevels = IEC61131Facade.file(CharStreams.fromStream(resource))
        IEC61131Facade.resolveDataTypes(toplevels)

        val globalScope = IEC61131Facade.resolveDataTypes(toplevels)
        val module = SymbExFacade.evaluateProgram(
                toplevels[2] as ProgramDeclaration,
                toplevels[0] as TypeDeclarations, globalScope)
        println(module)
        //System.out.println(state);
        //Assert.assertEquals();
    }
}
