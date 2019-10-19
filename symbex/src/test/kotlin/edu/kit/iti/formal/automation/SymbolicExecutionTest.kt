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
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.fail

private val SymbolicState.definitions: Map<String, String>
    get() = map.flatMap { (_, b) ->
        b.values.map { (a, b) -> a.name to b.repr() }
    }.toMap()

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
        val defs = state.definitions
        val states = state.stringifed

        assertThat(defs).run {
            containsEntry("a$0", "a")
            containsEntry("b$1", "b")
            containsEntry("c$2", "c")
            containsEntry("d$3", "d")
            containsEntry("e$4", "e")
            containsEntry("f$5", "f")
            containsEntry("o$6", "o")
            containsEntry("a$7", "0sd16_2")
            containsEntry("c$8", "0sd16_3")
            containsEntry("c$9", "a$7 + c$8")
            containsEntry("b$10", "0sd16_2 * a$7 + c$9")
        }
        assertThat(states).run {
            containsEntry("a", "a$7")
            containsEntry("b", "b$10")
            containsEntry("c", "c$9")
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
    fun simpleIfTest() {
        val statements = """
                    a := 2; 
                    c:= 4; 
                    b:=0; 
                    IF a = 2 THEN  b := 2; 
                    ELSE b := 1; c:=2; END_IF;"""
        val state = executeStatements(statements)
        val defs = state.definitions
        val states = state.stringifed

        defs.forEach { (t, u) -> println("$t = $u") }

        defs.run {
            containsEntry("a$0", "a")
            containsEntry("b$1", "b")
            containsEntry("c$2", "c")
            containsEntry("d$3", "d")
            containsEntry("e$4", "e")
            containsEntry("f$5", "f")
            containsEntry("o$6", "o")
            containsEntry("c$8", "0sd16_4")
            containsEntry("a$7", "0sd16_2")
            containsEntry("b$10", "0sd16_2")
            containsEntry("b$11", "0sd16_1")
            containsEntry("a$13", "a$7")
            containsEntry("b$14", "case a$7 = 0sd16_2 : b$10; TRUE : b$11; esac")
            containsEntry("b$9", "0sd16_0")
            containsEntry("c$12", "0sd16_2")
            containsEntry("c$15", "case  a$7 = 0sd16_2 : c$8; TRUE : c$12; esac")
            containsEntry("d$16", "d$3")
            containsEntry("e$17", "e$4")
            containsEntry("f$18", "f$5")
            containsEntry("o$19", "o$6")
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
        val defs = state.definitions
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
        val defs = state.definitions
        val states = state.stringifed
        defs.forEach { t, u -> println("containsEntry(\"$t\", \"${u.toString().replace("\n", "\\n")}\")") }
        states.forEach { t, u -> println("containsEntry(\"$t\", \"${u.toString().replace("\n", "\\n")}\")") }


        assertThat(defs).run {
            containsEntry("a$0", "a")
            containsEntry("a$11", "a$0")
            containsEntry("a$20", "a$0")
            containsEntry("a$28", "case\n    b$1 = 0sd16_0 : a$20; \n    TRUE : a$0; \nesac")
            containsEntry("a$35", "case\n    a$0 = 0sd16_0 : a$28; \n    TRUE : a$0; \nesac")
            containsEntry("a$42", "case\n    a$0 = 0sd16_1 | a$0 = 0sd16_2 : a$0; \n    a$0 = 0sd16_3 : a$11; \n    a$0 = 0sd16_4 | a$0 = 0sd16_5 | a$0 = 0sd16_6 : a$0; \n    TRUE : a$35; \nesac")
            containsEntry("b$1", "b")
            containsEntry("b$12", "b$1")
            containsEntry("b$21", "b$1")
            containsEntry("b$29", "case\n    b$1 = 0sd16_0 : b$21; \n    TRUE : b$1; \nesac")
            containsEntry("b$36", "case\n    a$0 = 0sd16_0 : b$29; \n    TRUE : b$1; \nesac")
            containsEntry("b$43", "case\n    a$0 = 0sd16_1 | a$0 = 0sd16_2 : b$1; \n    a$0 = 0sd16_3 : b$12; \n    a$0 = 0sd16_4 | a$0 = 0sd16_5 | a$0 = 0sd16_6 : b$1; \n    TRUE : b$36; \nesac")
            containsEntry("c$13", "c$2")
            containsEntry("c$2", "c")
            containsEntry("c$22", "c$2")
            containsEntry("c$30", "case\n    b$1 = 0sd16_0 : c$22; \n    TRUE : c$2; \nesac")
            containsEntry("c$37", "case\n    a$0 = 0sd16_0 : c$30; \n    TRUE : c$2; \nesac")
            containsEntry("c$44", "case\n    a$0 = 0sd16_1 | a$0 = 0sd16_2 : c$2; \n    a$0 = 0sd16_3 : c$13; \n    a$0 = 0sd16_4 | a$0 = 0sd16_5 | a$0 = 0sd16_6 : c$2; \n    TRUE : c$37; \nesac")
            containsEntry("d$14", "d$3")
            containsEntry("d$23", "d$3")
            containsEntry("d$3", "d")
            containsEntry("d$31", "case\n    b$1 = 0sd16_0 : d$23; \n    TRUE : d$3; \nesac")
            containsEntry("d$38", "case\n    a$0 = 0sd16_0 : d$31; \n    TRUE : d$3; \nesac")
            containsEntry("d$45", "case\n    a$0 = 0sd16_1 | a$0 = 0sd16_2 : d$3; \n    a$0 = 0sd16_3 : d$14; \n    a$0 = 0sd16_4 | a$0 = 0sd16_5 | a$0 = 0sd16_6 : d$3; \n    TRUE : d$38; \nesac")
            containsEntry("e$15", "e$4")
            containsEntry("e$24", "e$4")
            containsEntry("e$32", "case\n    b$1 = 0sd16_0 : e$24; \n    TRUE : e$4; \nesac")
            containsEntry("e$39", "case\n    a$0 = 0sd16_0 : e$32; \n    TRUE : e$4; \nesac")
            containsEntry("e$4", "e")
            containsEntry("e$46", "case\n    a$0 = 0sd16_1 | a$0 = 0sd16_2 : e$4; \n    a$0 = 0sd16_3 : e$15; \n    a$0 = 0sd16_4 | a$0 = 0sd16_5 | a$0 = 0sd16_6 : e$4; \n    TRUE : e$39; \nesac")
            containsEntry("f$16", "f$5")
            containsEntry("f$25", "f$5")
            containsEntry("f$33", "case\n    b$1 = 0sd16_0 : f$25; \n    TRUE : f$5; \nesac")
            containsEntry("f$40", "case\n    a$0 = 0sd16_0 : f$33; \n    TRUE : f$5; \nesac")
            containsEntry("f$47", "case\n    a$0 = 0sd16_1 | a$0 = 0sd16_2 : f$5; \n    a$0 = 0sd16_3 : f$16; \n    a$0 = 0sd16_4 | a$0 = 0sd16_5 | a$0 = 0sd16_6 : f$5; \n    TRUE : f$40; \nesac")
            containsEntry("f$5", "f")
            containsEntry("o$10", "0sd16_2 * a$0 + 0sd16_2 * b$1")
            containsEntry("o$17", "case\n    b$1 = 0sd16_0 : o$9; \n    TRUE : o$10; \nesac")
            containsEntry("o$18", "0sd16_4")
            containsEntry("o$19", "0sd16_0")
            containsEntry("o$26", "case\n    c$2 = 0sd16_0 : o$19; \n    TRUE : o$6; \nesac")
            containsEntry("o$27", "0sd16_0")
            containsEntry("o$34", "case\n    b$1 = 0sd16_0 : o$26; \n    TRUE : o$27; \nesac")
            containsEntry("o$41", "case\n    a$0 = 0sd16_0 : o$34; \n    TRUE : o$6; \nesac")
            containsEntry("o$48", "case\n    a$0 = 0sd16_1 : o$7; \n    a$0 = 0sd16_2 : o$8; \n    a$0 = 0sd16_3 : o$17; \n    a$0 = 0sd16_4 | a$0 = 0sd16_5 | a$0 = 0sd16_6 : o$18; \n    TRUE : o$41; \nesac")
            containsEntry("o$6", "o")
            containsEntry("o$7", "0sd16_1")
            containsEntry("o$8", "0sd16_2")
            containsEntry("o$9", "a$0 + b$1")
        }
        val uf = state.unfolded().stringifed
        println(uf)
    }


    @Test
    fun simpleAssignmentTest() {
        val statements = "a := 2;\na := 3;\na:= 4;\nb := a + 1;\nb := a + 1;\nb := b + 1;"
        val state = executeStatements(statements)
        val definitions = state.definitions

        assertThat(definitions).run {
            containsEntry("a$0", "a")
            containsEntry("b$1", "b")
            containsEntry("c$2", "c")
            containsEntry("d$3", "d")
            containsEntry("e$4", "e")
            containsEntry("f$5", "f")
            containsEntry("o$6", "o")
            containsEntry("a$7", "0sd16_2")
            containsEntry("a$8", "0sd16_3")
            containsEntry("a$9", "0sd16_4")
            containsEntry("b$10", "a$9 + 0sd16_1")
            containsEntry("b$11", "a$9 + 0sd16_1")
            containsEntry("b$12", "b$11 + 0sd16_1")
        }

        assertThat(state.stringifed).let {
            it.containsEntry("a", "a$9")
            it.containsEntry("b", "b$12")
        }

        val uf = state.unfolded().stringifed
        assertThat(uf).run {
            containsEntry("a", "0sd16_4")
            containsEntry("b", "0sd16_4 + 0sd16_1 + 0sd16_1")
        }
    }

    private fun executeStatements(statements: String): SymbolicState {
        val list = IEC61131Facade.statements(statements)
        IEC61131Facade.resolveDataTypes(elements = *arrayOf(list))
        return SymbExFacade.evaluateStatements(list, scope)
    }
}

internal fun String.cleanWhitespace(): String = replace("[ \n\t\r]+".toRegex(), " ")
