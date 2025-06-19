/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
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
 * *****************************************************************/
package edu.kit.iti.formal.automation

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
                if (b is SymbolicVariableTracing) {
                    b.values.entries.asSequence().map { (a, b) -> a.repr() to b.repr() }
                } else {
                    listOf(a.repr() to b.value.repr()).asSequence()
                }
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
            containsEntry("a$00013", "a$00007")
            containsEntry("b$00014", "case a$00007 = 0sd16_2 : b$00010; TRUE : b$00011; esac")
            containsEntry("b$00009", "0sd16_0")
            containsEntry("c$00012", "0sd16_2")
            containsEntry("c$00015", "case  a$00007 = 0sd16_2 : c$00008; TRUE : c$00012; esac")
            containsEntry("d$00016", "d$00003")
            containsEntry("e$00017", "e$00004")
            containsEntry("f$00018", "f$00005")
            containsEntry("o$00019", "o$00006")
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
        val state = executeStatements(list)
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
        // defs.forEach { t, u -> println("containsEntry(\"$t\", \"${u.toString().replace("\n", "\\n")}\")") }
        // states.forEach { t, u -> println("containsEntry(\"$t\", \"${u.toString().replace("\n", "\\n")}\")") }

        assertThat(defs).run {
            containsEntry("a$00000", "a")
            containsEntry("a$00011", "a$00000")
            containsEntry("a$00020", "a$00000")
            containsEntry("a$00028", "case\n    b$00001 = 0sd16_0 : a$00020; \n    TRUE : a$00000; \nesac")
            containsEntry("a$00035", "case\n    a$00000 = 0sd16_0 : a$00028; \n    TRUE : a$00000; \nesac")
            containsEntry(
                "a$00042",
                "case\n    a$00000 = 0sd16_1 | a$00000 = 0sd16_2 : a$00000; \n    a$00000 = 0sd16_3 : a$00011; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : a$00000; \n    TRUE : a$00035; \nesac",
            )
            containsEntry("b$00001", "b")
            containsEntry("b$00012", "b$00001")
            containsEntry("b$00021", "b$00001")
            containsEntry("b$00029", "case\n    b$00001 = 0sd16_0 : b$00021; \n    TRUE : b$00001; \nesac")
            containsEntry("b$00036", "case\n    a$00000 = 0sd16_0 : b$00029; \n    TRUE : b$00001; \nesac")
            containsEntry(
                "b$00043",
                "case\n    a$00000 = 0sd16_1 | a$00000 = 0sd16_2 : b$00001; \n    a$00000 = 0sd16_3 : b$00012; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : b$00001; \n    TRUE : b$00036; \nesac",
            )
            containsEntry("c$00002", "c")
            containsEntry("c$00013", "c$00002")
            containsEntry("c$00022", "c$00002")
            containsEntry("c$00030", "case\n    b$00001 = 0sd16_0 : c$00022; \n    TRUE : c$00002; \nesac")
            containsEntry("c$00037", "case\n    a$00000 = 0sd16_0 : c$00030; \n    TRUE : c$00002; \nesac")
            containsEntry(
                "c$00044",
                "case\n    a$00000 = 0sd16_1 | a$00000 = 0sd16_2 : c$00002; \n    a$00000 = 0sd16_3 : c$00013; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : c$00002; \n    TRUE : c$00037; \nesac",
            )
            containsEntry("d$00003", "d")
            containsEntry("d$00014", "d$00003")
            containsEntry("d$00023", "d$00003")
            containsEntry("d$00031", "case\n    b$00001 = 0sd16_0 : d$00023; \n    TRUE : d$00003; \nesac")
            containsEntry("d$00038", "case\n    a$00000 = 0sd16_0 : d$00031; \n    TRUE : d$00003; \nesac")
            containsEntry(
                "d$00045",
                "case\n    a$00000 = 0sd16_1 | a$00000 = 0sd16_2 : d$00003; \n    a$00000 = 0sd16_3 : d$00014; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : d$00003; \n    TRUE : d$00038; \nesac",
            )
            containsEntry("e$00004", "e")
            containsEntry("e$00015", "e$00004")
            containsEntry("e$00024", "e$00004")
            containsEntry("e$00032", "case\n    b$00001 = 0sd16_0 : e$00024; \n    TRUE : e$00004; \nesac")
            containsEntry("e$00039", "case\n    a$00000 = 0sd16_0 : e$00032; \n    TRUE : e$00004; \nesac")
            containsEntry(
                "e$00046",
                "case\n    a$00000 = 0sd16_1 | a$00000 = 0sd16_2 : e$00004; \n    a$00000 = 0sd16_3 : e$00015; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : e$00004; \n    TRUE : e$00039; \nesac",
            )
            containsEntry("f$00005", "f")
            containsEntry("f$00016", "f$00005")
            containsEntry("f$00025", "f$00005")
            containsEntry("f$00033", "case\n    b$00001 = 0sd16_0 : f$00025; \n    TRUE : f$00005; \nesac")
            containsEntry("f$00040", "case\n    a$00000 = 0sd16_0 : f$00033; \n    TRUE : f$00005; \nesac")
            containsEntry(
                "f$00047",
                "case\n    a$00000 = 0sd16_1 | a$00000 = 0sd16_2 : f$00005; \n    a$00000 = 0sd16_3 : f$00016; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : f$00005; \n    TRUE : f$00040; \nesac",
            )
            containsEntry("o$00006", "o")
            containsEntry("o$00007", "0sd16_1")
            containsEntry("o$00008", "0sd16_2")
            containsEntry("o$00009", "a$00000 + b$00001")
            containsEntry("o$00010", "0sd16_2 * a$00000 + 0sd16_2 * b$00001")
            containsEntry("o$00018", "0sd16_4")
            containsEntry("o$00019", "0sd16_0")
            containsEntry("o$00027", "0sd16_0")
            containsEntry("o$00017", "case\n    b$00001 = 0sd16_0 : o$00009; \n    TRUE : o$00010; \nesac")
            containsEntry("o$00026", "case\n    c$00002 = 0sd16_0 : o$00019; \n    TRUE : o$00006; \nesac")
            containsEntry("o$00034", "case\n    b$00001 = 0sd16_0 : o$00026; \n    TRUE : o$00027; \nesac")
            containsEntry("o$00041", "case\n    a$00000 = 0sd16_0 : o$00034; \n    TRUE : o$00006; \nesac")
            containsEntry(
                "o$00048",
                "case\n    a$00000 = 0sd16_1 : o$00007; \n    a$00000 = 0sd16_2 : o$00008; \n    a$00000 = 0sd16_3 : o$00017; \n    a$00000 = 0sd16_4 | a$00000 = 0sd16_5 | a$00000 = 0sd16_6 : o$00018; \n    TRUE : o$00041; \nesac",
            )
        }
        assertThat(states).run {
            containsEntry("a", "a$00042")
            containsEntry("b", "b$00043")
            containsEntry("c", "c$00044")
            containsEntry("d", "d$00045")
            containsEntry("e", "e$00046")
            containsEntry("f", "f$00047")
            containsEntry("o", "o$00048")
        }
        // val uf = state.unfolded().stringifed
        // println(uf)
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

    private fun executeStatements(statements: String, useDefs: Boolean = true): SymbolicState {
        val list = IEC61131Facade.statements(statements)
        IEC61131Facade.resolveDataTypes(elements = *arrayOf(list))
        return SymbExFacade.evaluateStatements(list, scope, useDefs)
    }
}

internal fun String.cleanWhitespace(): String = replace("[ \n\t\r]+".toRegex(), " ")