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
            containsEntry("a_0", "a")
            containsEntry("b_1", "b")
            containsEntry("c_2", "c")
            containsEntry("d_3", "d")
            containsEntry("e_4", "e")
            containsEntry("f_5", "f")
            containsEntry("o_6", "o")
            containsEntry("a_7", "0sd16_2")
            containsEntry("c_8", "0sd16_3")
            containsEntry("c_9", "a_7 + c_8")
            containsEntry("b_10", "0sd16_2 * a_7 + c_9")
        }
        assertThat(states).run {
            containsEntry("a", "a_7")
            containsEntry("b", "b_10")
            containsEntry("c", "c_9")
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
            containsEntry("a_0", "a")
            containsEntry("b_1", "b")
            containsEntry("c_2", "c")
            containsEntry("d_3", "d")
            containsEntry("e_4", "e")
            containsEntry("f_5", "f")
            containsEntry("o_6", "o")
            containsEntry("c_8", "0sd16_4")
            containsEntry("a_7", "0sd16_2")
            containsEntry("b_10", "0sd16_2")
            containsEntry("b_11", "0sd16_1")
            containsEntry("a_13", "a_7")
            containsEntry("b_14", "case a_7 = 0sd16_2 : b_10; TRUE : b_11; esac")
            containsEntry("b_9", "0sd16_0")
            containsEntry("c_12", "0sd16_2")
            containsEntry("c_15", "case  a_7 = 0sd16_2 : c_8; TRUE : c_12; esac")
            containsEntry("d_16", "d_3")
            containsEntry("e_17", "e_4")
            containsEntry("f_18", "f_5")
            containsEntry("o_19", "o_6")
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
            containsEntry("a_0", "a")
            containsEntry("a_11", "a_0")
            containsEntry("a_20", "a_0")
            containsEntry("a_28", "case\n    b_1 = 0sd16_0 : a_20; \n    TRUE : a_0; \nesac")
            containsEntry("a_35", "case\n    a_0 = 0sd16_0 : a_28; \n    TRUE : a_0; \nesac")
            containsEntry("a_42", "case\n    a_0 = 0sd16_1 | a_0 = 0sd16_2 : a_0; \n    a_0 = 0sd16_3 : a_11; \n    a_0 = 0sd16_4 | a_0 = 0sd16_5 | a_0 = 0sd16_6 : a_0; \n    TRUE : a_35; \nesac")
            containsEntry("b_1", "b")
            containsEntry("b_12", "b_1")
            containsEntry("b_21", "b_1")
            containsEntry("b_29", "case\n    b_1 = 0sd16_0 : b_21; \n    TRUE : b_1; \nesac")
            containsEntry("b_36", "case\n    a_0 = 0sd16_0 : b_29; \n    TRUE : b_1; \nesac")
            containsEntry("b_43", "case\n    a_0 = 0sd16_1 | a_0 = 0sd16_2 : b_1; \n    a_0 = 0sd16_3 : b_12; \n    a_0 = 0sd16_4 | a_0 = 0sd16_5 | a_0 = 0sd16_6 : b_1; \n    TRUE : b_36; \nesac")
            containsEntry("c_13", "c_2")
            containsEntry("c_2", "c")
            containsEntry("c_22", "c_2")
            containsEntry("c_30", "case\n    b_1 = 0sd16_0 : c_22; \n    TRUE : c_2; \nesac")
            containsEntry("c_37", "case\n    a_0 = 0sd16_0 : c_30; \n    TRUE : c_2; \nesac")
            containsEntry("c_44", "case\n    a_0 = 0sd16_1 | a_0 = 0sd16_2 : c_2; \n    a_0 = 0sd16_3 : c_13; \n    a_0 = 0sd16_4 | a_0 = 0sd16_5 | a_0 = 0sd16_6 : c_2; \n    TRUE : c_37; \nesac")
            containsEntry("d_14", "d_3")
            containsEntry("d_23", "d_3")
            containsEntry("d_3", "d")
            containsEntry("d_31", "case\n    b_1 = 0sd16_0 : d_23; \n    TRUE : d_3; \nesac")
            containsEntry("d_38", "case\n    a_0 = 0sd16_0 : d_31; \n    TRUE : d_3; \nesac")
            containsEntry("d_45", "case\n    a_0 = 0sd16_1 | a_0 = 0sd16_2 : d_3; \n    a_0 = 0sd16_3 : d_14; \n    a_0 = 0sd16_4 | a_0 = 0sd16_5 | a_0 = 0sd16_6 : d_3; \n    TRUE : d_38; \nesac")
            containsEntry("e_15", "e_4")
            containsEntry("e_24", "e_4")
            containsEntry("e_32", "case\n    b_1 = 0sd16_0 : e_24; \n    TRUE : e_4; \nesac")
            containsEntry("e_39", "case\n    a_0 = 0sd16_0 : e_32; \n    TRUE : e_4; \nesac")
            containsEntry("e_4", "e")
            containsEntry("e_46", "case\n    a_0 = 0sd16_1 | a_0 = 0sd16_2 : e_4; \n    a_0 = 0sd16_3 : e_15; \n    a_0 = 0sd16_4 | a_0 = 0sd16_5 | a_0 = 0sd16_6 : e_4; \n    TRUE : e_39; \nesac")
            containsEntry("f_16", "f_5")
            containsEntry("f_25", "f_5")
            containsEntry("f_33", "case\n    b_1 = 0sd16_0 : f_25; \n    TRUE : f_5; \nesac")
            containsEntry("f_40", "case\n    a_0 = 0sd16_0 : f_33; \n    TRUE : f_5; \nesac")
            containsEntry("f_47", "case\n    a_0 = 0sd16_1 | a_0 = 0sd16_2 : f_5; \n    a_0 = 0sd16_3 : f_16; \n    a_0 = 0sd16_4 | a_0 = 0sd16_5 | a_0 = 0sd16_6 : f_5; \n    TRUE : f_40; \nesac")
            containsEntry("f_5", "f")
            containsEntry("o_10", "0sd16_2 * a_0 + 0sd16_2 * b_1")
            containsEntry("o_17", "case\n    b_1 = 0sd16_0 : o_9; \n    TRUE : o_10; \nesac")
            containsEntry("o_18", "0sd16_4")
            containsEntry("o_19", "0sd16_0")
            containsEntry("o_26", "case\n    c_2 = 0sd16_0 : o_19; \n    TRUE : o_6; \nesac")
            containsEntry("o_27", "0sd16_0")
            containsEntry("o_34", "case\n    b_1 = 0sd16_0 : o_26; \n    TRUE : o_27; \nesac")
            containsEntry("o_41", "case\n    a_0 = 0sd16_0 : o_34; \n    TRUE : o_6; \nesac")
            containsEntry("o_48", "case\n    a_0 = 0sd16_1 : o_7; \n    a_0 = 0sd16_2 : o_8; \n    a_0 = 0sd16_3 : o_17; \n    a_0 = 0sd16_4 | a_0 = 0sd16_5 | a_0 = 0sd16_6 : o_18; \n    TRUE : o_41; \nesac")
            containsEntry("o_6", "o")
            containsEntry("o_7", "0sd16_1")
            containsEntry("o_8", "0sd16_2")
            containsEntry("o_9", "a_0 + b_1")
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
            containsEntry("a_0", "a")
            containsEntry("b_1", "b")
            containsEntry("c_2", "c")
            containsEntry("d_3", "d")
            containsEntry("e_4", "e")
            containsEntry("f_5", "f")
            containsEntry("o_6", "o")
            containsEntry("a_7", "0sd16_2")
            containsEntry("a_8", "0sd16_3")
            containsEntry("a_9", "0sd16_4")
            containsEntry("b_10", "a_9 + 0sd16_1")
            containsEntry("b_11", "a_9 + 0sd16_1")
            containsEntry("b_12", "b_11 + 0sd16_1")
        }

        assertThat(state.stringifed).let {
            it.containsEntry("a", "a_9")
            it.containsEntry("b", "b_12")
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
