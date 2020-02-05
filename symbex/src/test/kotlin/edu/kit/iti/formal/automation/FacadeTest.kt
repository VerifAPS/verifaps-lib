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

import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration
import edu.kit.iti.formal.smv.ast.SVariable
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assumptions
import org.junit.jupiter.api.Test
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
        Assumptions.assumeTrue(null != resource)
        val (toplevels, error) = IEC61131Facade.fileResolve(CharStreams.fromStream(resource))
        val func = toplevels[0] as FunctionDeclaration
        val state = SymbExFacade.evaluateFunction(func,
                SVariable.create("a").asBool(),
                SVariable.create("b").asBool(),
                SVariable.create("c").asBool())
        //System.out.println(state);
        Assertions.assertNotEquals(null, state)
        Assertions.assertEquals("case a : b; TRUE : c; esac".cleanWhitespace(),
                state.repr().cleanWhitespace())
    }

    @Test
    @Throws(IOException::class)
    fun testModuleBuilder() {
        val resource = javaClass.getResourceAsStream("/edu/kit/iti/formal/automation/st/symbextest.st")
        val (toplevels, ok) = IEC61131Facade.fileResolve(CharStreams.fromStream(resource))
        val module = SymbExFacade.evaluateProgram(toplevels[2] as ProgramDeclaration)
        println(module)
        //System.out.println(state);
        //Assertions.assertEquals();
    }

    @Test
    fun testExecute() {
        val resource = javaClass.getResourceAsStream("/edu/kit/iti/formal/automation/st/symbextest.st")
        val (toplevels, ok) = IEC61131Facade.fileResolve(CharStreams.fromStream(resource))
        val p = toplevels[2] as ProgramDeclaration
        try {
            val ttp = SymbExFacade.execute(p)
            for (i in 1..9) {
                println(ttp.get(i))
            }
        }catch (e : IOException) {
            Assumptions.assumeTrue(e.message?.startsWith("Cannot run program") ?: false)
        }
    }
}

