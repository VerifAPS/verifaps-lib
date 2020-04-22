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

import com.google.common.truth.Truth.assertThat
import edu.kit.iti.formal.automation.datatypes.INT
import edu.kit.iti.formal.automation.rvt.SymbolicState
import edu.kit.iti.formal.automation.rvt.SymbolicVariable
import edu.kit.iti.formal.automation.rvt.SymbolicVariableTracing
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.fail

private val Map<SVariable, SymbolicVariable>.stringified: Map<String, String>
    get() =
        asSequence()
                .flatMap { (a, b) ->
                    if (b is SymbolicVariableTracing)
                        b.values.entries.asSequence().map { (a, b) -> a.repr() to b.repr() }
                    else
                        listOf(a.repr() to b.value.repr()).asSequence()
                }
                .toMap()

/*private val SymbolicState.definitions: Map<String, String>
    get() = variables.flatMap { (_, b) ->
        if (b is SymbolicVariableTracing)
            b.values.map { (a, b) -> a.name to b.repr() }
        else
            emptySet()
    }.toMap()
*/

private val Map<SVariable, SMVExpr>.stringifed: Map<String, String>
    get() = asSequence()
            .map { (a, b) -> a.name to b.repr() }
            .toMap()

/**
 * @author Alexander Weigl
 * @version 1 (27.11.16)
 * @version 2 (18.08.19)
 */
class SymbolicExecutionTest {
    val scope = arrayOf("a", "b", "c", "d", "e", "f", "o")
            .map { VariableDeclaration(it, 0, INT) }
            .let { Scope(it) }

    @Test
    fun simpleTest() {
        val statments = "a := 2;" +
                "c := 3;" +
                "c := a+c;" +
                "b := 2*a+c;"
        val state = executeStatements(statments)
        val defs = state.variables.stringified
        val states = state.stringifed

        assertThat(defs).run {
            containsEntry("a$00000", "a")
            containsEntry("b$00001", "b")
            containsEntry("c$00002", "c")
            containsEntry("d$00003", "d")
            containsEntry("e$00004", "e")
            containsEntry("f$00005", "f")
            containsEntry("o$00006", "o")
            containsEntry("a$00007", "0sd16_2")
            containsEntry("c$00008", "0sd16_3")
            containsEntry("c$00009", "a$00007 + c$00008")
            containsEntry("b$00010", "0sd16_2 * a$00007 + c$00009")
        }
        assertThat(states).run {
            containsEntry("a", "a$00007")
            containsEntry("b", "b$00010")
            containsEntry("c", "c$00009")
        }

        val uf = state.unfolded().stringifed
        assertThat(uf).run {
            containsEntry("a", "0sd16_2")
            containsEntry("b", "0sd16_2 * 0sd16_2 + 0sd16_2 + 0sd16_3")
            containsEntry("c", "0sd16_2 + 0sd16_3")
            containsEntry("d", "d")
            containsEntry("e", "e")
            containsEntry("f", "f")
            containsEntry("o", "o")
        }
    }

    @Test
    fun simpleTestNoDefs() {
        val statments = "a := 2;" +
                "c := 3;" +
                "c := a+c;" +
                "b := 2*a+c;"
        val state = executeStatements(statments, false)
        val defs = state.variables.stringified
        val states = state.stringifed

        println(defs)
        println(states)

        assertThat(states).run {
            containsEntry("a", "0sd16_2")
            containsEntry("b", "0sd16_2 * 0sd16_2 + 0sd16_2 + 0sd16_3")
            containsEntry("c", "0sd16_2 + 0sd16_3")
            containsEntry("d", "d")
            containsEntry("e", "e")
            containsEntry("f", "f")
            containsEntry("o", "o")
            isEqualTo(states)
        }
    }

    @Test
    fun simpleIfTest() {
        val statements = """
                    a := 2; 
                    c:= 4; 
                    b:=0; 
                    IF a = 2 THEN  b := 2; 
                    ELSE b := 1; c:=2; END_IF;"""
        val state = executeStatements(statements)
        val defs = state.variables.stringified
        val states = state.stringifed

        defs.forEach { (t, u) -> println("$t = $u") }

        defs.run {
            containsEntry("a$00000", "a")
            containsEntry("b$00001", "b")
            containsEntry("c$00002", "c")
            containsEntry("d$00003", "d")
            containsEntry("e$00004", "e")
            containsEntry("f$00005", "f")
            containsEntry("o$00006", "o")
            containsEntry("c$00008", "0sd16_4")
            containsEntry("a$00007", "0sd16_2")
            containsEntry("b$00010", "0sd16_2")
            containsEntry("b$00011", "0sd16_1")
            containsEntry("a$13", "a$00007")
            containsEntry("b$14", "case a$00007 = 0sd16_2 : b$00010; TRUE : b$00011; esac")
            containsEntry("b$00009", "0sd16_0")
            containsEntry("c$00012", "0sd16_2")
            containsEntry("c$15", "case  a$00007 = 0sd16_2 : c$00008; TRUE : c$00012; esac")
            containsEntry("d$16", "d$00003")
            containsEntry("e$17", "e$00004")
            containsEntry("f$18", "f$00005")
            containsEntry("o$19", "o$00006")
        }

        val uf = state.unfolded().stringifed
        uf.run {
            containsEntry("a", "0sd16_2")
            containsEntry("b", "case 0sd16_2 = 0sd16_2 : 0sd16_2; TRUE : 0sd16_1; esac")
            containsEntry("c", "case 0sd16_2 = 0sd16_2 : 0sd16_4; TRUE : 0sd16_2; esac")
        }
    }

    private fun Map<String, String>.containsEntry(key: String, value: String) {
        val s = this[key] ?: fail("Entry $key is empty. Map is $this")
        Assertions.assertTrue(s.isNotBlank())
        Assertions.assertEquals(value.cleanWhitespace(), s.cleanWhitespace())
    }

    @Test
    fun simpleIfWithoutElse() {
        val list = "a := 1; c:= a; b:=b; IF a = 2 THEN b := 2; c := 1;END_IF;"
        val state = executeStatements(list);
        val defs = state.variables
        val states = state.stringifed
        defs.forEach { t, u -> println("containsEntry(\"$t\", \"${u.toString().replace("\n", "\\n")}\")") }
        states.forEach { t, u -> println("containsEntry(\"$t\", \"${u.toString().replace("\n", "\\n")}\")") }

    }

    @Test
    fun complex() {
        val list = """
            CASE a OF
            1: o := 1;
            2: o := 2;
            3: 
                IF b = 0 THEN
                    o := a + b;
                ELSE
                    o := 2*a+2*b;
                END_IF
            4,5,6: o:= 4;
            ELSE
                IF a = 0 THEN
                    IF b = 0 THEN
                        IF c = 0 THEN
                            o := 0;
                        END_IF 
                    ELSE
                        o := 0;
                    END_IF 
                END_IF
         END_CASE
        """.trimIndent()
        val state = executeStatements(list)
        val defs = state.variables.stringified
        val states = state.stringifed
        //defs.forEach { t, u -> println("containsEntry(\"$t\", \"${u.toString().replace("\n", "\\n")}\")") }
        //states.forEach { t, u -> println("containsEntry(\"$t\", \"${u.toString().replace("\n", "\\n")}\")") }


        assertThat(defs).run {
            containsEntry("a$00000", "a")
            containsEntry("a$11", "a$00000")
            containsEntry("a$20", "a$00000")
            containsEntry("a$28", "case\n    b$00001 = 0sd16_0 : a$20; \n    TRUE : a$00000; \nesac")
            containsEntry("a$35", "case\n    a$00000 = 0sd16_0 : a$28; \n    TRUE : a$00000; \nesac")
            containsEntry("a$42", "case\n    a$00000 = 0sd16_1 | a$00000 = 0sd16_2 : a$00000; \n    a$00000 = 0sd16_3 : a$11; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : a$00000; \n    TRUE : a$35; \nesac")
            containsEntry("b$00001", "b")
            containsEntry("b$12", "b$00001")
            containsEntry("b$21", "b$00001")
            containsEntry("b$29", "case\n    b$00001 = 0sd16_0 : b$21; \n    TRUE : b$00001; \nesac")
            containsEntry("b$36", "case\n    a$00000 = 0sd16_0 : b$29; \n    TRUE : b$00001; \nesac")
            containsEntry("b$43", "case\n    a$00000 = 0sd16_1 | a$00000 = 0sd16_2 : b$00001; \n    a$00000 = 0sd16_3 : b$12; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : b$00001; \n    TRUE : b$36; \nesac")
            containsEntry("c$00002", "c")
            containsEntry("c$13", "c$00002")
            containsEntry("c$22", "c$00002")
            containsEntry("c$30", "case\n    b$00001 = 0sd16_0 : c$22; \n    TRUE : c$00002; \nesac")
            containsEntry("c$37", "case\n    a$00000 = 0sd16_0 : c$30; \n    TRUE : c$00002; \nesac")
            containsEntry("c$44", "case\n    a$00000 = 0sd16_1 | a$00000 = 0sd16_2 : c$00002; \n    a$00000 = 0sd16_3 : c$13; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : c$00002; \n    TRUE : c$37; \nesac")
            containsEntry("d$00003", "d")
            containsEntry("d$14", "d$00003")
            containsEntry("d$23", "d$00003")
            containsEntry("d$31", "case\n    b$00001 = 0sd16_0 : d$23; \n    TRUE : d$00003; \nesac")
            containsEntry("d$38", "case\n    a$00000 = 0sd16_0 : d$31; \n    TRUE : d$00003; \nesac")
            containsEntry("d$45", "case\n    a$00000 = 0sd16_1 | a$00000 = 0sd16_2 : d$00003; \n    a$00000 = 0sd16_3 : d$14; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : d$00003; \n    TRUE : d$38; \nesac")
            containsEntry("e$00004", "e")
            containsEntry("e$15", "e$00004")
            containsEntry("e$24", "e$00004")
            containsEntry("e$32", "case\n    b$00001 = 0sd16_0 : e$24; \n    TRUE : e$00004; \nesac")
            containsEntry("e$39", "case\n    a$00000 = 0sd16_0 : e$32; \n    TRUE : e$00004; \nesac")
            containsEntry("e$46", "case\n    a$00000 = 0sd16_1 | a$00000 = 0sd16_2 : e$00004; \n    a$00000 = 0sd16_3 : e$15; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : e$00004; \n    TRUE : e$39; \nesac")
            containsEntry("f$00005", "f")
            containsEntry("f$16", "f$00005")
            containsEntry("f$25", "f$00005")
            containsEntry("f$33", "case\n    b$00001 = 0sd16_0 : f$25; \n    TRUE : f$00005; \nesac")
            containsEntry("f$40", "case\n    a$00000 = 0sd16_0 : f$33; \n    TRUE : f$00005; \nesac")
            containsEntry("f$47", "case\n    a$00000 = 0sd16_1 | a$00000 = 0sd16_2 : f$00005; \n    a$00000 = 0sd16_3 : f$16; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : f$00005; \n    TRUE : f$40; \nesac")
            containsEntry("o$00006", "o")
            containsEntry("o$00007", "0sd16_1")
            containsEntry("o$00008", "0sd16_2")
            containsEntry("o$00009", "a$00000 + b$00001")
            containsEntry("o$00010", "0sd16_2 * a$00000 + 0sd16_2 * b$00001")
            containsEntry("o$00018", "0sd16_4")
            containsEntry("o$00019", "0sd16_0")
            containsEntry("o$00027", "0sd16_0")
            containsEntry("o$17", "case\n    b$00001 = 0sd16_0 : o$00009; \n    TRUE : o$00010; \nesac")
            containsEntry("o$26", "case\n    c$00002 = 0sd16_0 : o$00019; \n    TRUE : o$00006; \nesac")
            containsEntry("o$34", "case\n    b$00001 = 0sd16_0 : o$26; \n    TRUE : o$00027; \nesac")
            containsEntry("o$41", "case\n    a$00000 = 0sd16_0 : o$34; \n    TRUE : o$00006; \nesac")
            containsEntry("o$48", "case\n    a$00000 = 0sd16_1 : o$00007; \n    a$00000 = 0sd16_2 : o$00008; \n    a$00000 = 0sd16_3 : o$17; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : o$00018; \n    TRUE : o$41; \nesac")
        }
        assertThat(states).run {
            containsEntry("a", "a$42")
            containsEntry("b", "b$43")
            containsEntry("c", "c$44")
            containsEntry("d", "d$45")
            containsEntry("e", "e$46")
            containsEntry("f", "f$47")
            containsEntry("o", "o$48")
        }
        //val uf = state.unfolded().stringifed
        //println(uf)
    }


    @Test
    fun simpleAssignmentTest() {
        val statements = "a := 2;\na := 3;\na:= 4;\nb := a + 1;\nb := a + 1;\nb := b + 1;"
        val state = executeStatements(statements)
        val definitions = state.variables.stringified

        assertThat(definitions).run {
            containsEntry("a$00000", "a")
            containsEntry("b$00001", "b")
            containsEntry("c$00002", "c")
            containsEntry("d$00003", "d")
            containsEntry("e$00004", "e")
            containsEntry("f$00005", "f")
            containsEntry("o$00006", "o")
            containsEntry("a$00007", "0sd16_2")
            containsEntry("a$00008", "0sd16_3")
            containsEntry("a$00009", "0sd16_4")
            containsEntry("b$00010", "a$00009 + 0sd16_1")
            containsEntry("b$00011", "a$00009 + 0sd16_1")
            containsEntry("b$00012", "b$00011 + 0sd16_1")
        }

        assertThat(state.stringifed).let {
            it.containsEntry("a", "a$00009")
            it.containsEntry("b", "b$00012")
        }

        val uf = state.unfolded().stringifed
        assertThat(uf).run {
            containsEntry("a", "0sd16_4")
            containsEntry("b", "0sd16_4 + 0sd16_1 + 0sd16_1")
        }
    }

    private fun executeStatements(statements: String, useDefs: Boolean=true): SymbolicState {
        val list = IEC61131Facade.statements(statements)
        IEC61131Facade.resolveDataTypes(elements = *arrayOf(list))
        return SymbExFacade.evaluateStatements(list, scope, useDefs)
    }
}

internal fun String.cleanWhitespace(): String = replace("[ \n\t\r]+".toRegex(), " ")
