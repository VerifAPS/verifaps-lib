package edu.kit.iti.formal.stvs.logic.specification.smtlib

import com.google.common.truth.Truth
import edu.kit.iti.formal.smt.SExprFacade.sexpr
import edu.kit.iti.formal.smt.SList
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import java.util.regex.Pattern

/**
 * Created by csicar on 02.03.17.
 */
class SmtModelTest {
    private lateinit var simple: SmtModel
    private lateinit var other: SmtModel

    private fun fromString(vars: String, constr: String) =
        SmtModel((fromText("($constr)") as SList), (fromText("($vars)") as SList))

    private fun assertMatches(pattern: String, string: String?) {
        val escapedPattern = "\\s?" + pattern
            .replace(" ", "\\s+")
            .replace("(", "\\(")
            .replace(")", "\\)") + "\\s?"
        Assertions.assertTrue(
            Pattern.matches(escapedPattern, string),
            "Tried to match <<$string>> with $escapedPattern"
        )
    }

    @BeforeEach
    fun setup() {
        this.simple = fromString(
            "a bb ccc",
            "d ee fff"
        )
        this.other = fromString(
            "l o s",
            "ggg (1 2 3 h) i"
        )
    }

    @Test
    fun combine() {
        simple.combine(other)
        Assertions.assertEquals(
            fromString(
                "a bb ccc l o s",
                "d ee fff ggg (1 2 3 h) i"
            ), simple
        )
    }

    @Test
    @Throws(Exception::class)
    fun toSexpr() {
        Truth.assertThat(simple.toSexpr())
            .isEqualTo(fromText("(a bb ccc ( assert d ) ( assert ee ) ( assert fff) )"))
    }

    @Test
    @Throws(Exception::class)
    fun headerToText() {
        val result = simple.headerToText()
        assertMatches("a bb ccc", result)

        val result2 = other.headerToText()
        println(result2)
        assertMatches("l o s", result2)
    }

    @Test
    @Throws(Exception::class)
    fun addGlobalConstrainsAsArguments() {
        simple.addGlobalConstraint(sym("new"))
        simple.addGlobalConstraint(sym("new2"))
        Assertions.assertEquals(
            fromString(
                "a bb ccc",
                "d ee fff new new2"
            ), simple
        )
        other.addGlobalConstraint(SList("newA", sexpr("newB", "newC")))
        Assertions.assertEquals(
            fromString(
                "l o s",
                "ggg (1 2 3 h) i (newA (newB newC))"
            ), other
        )
    }

    @Test
    @Throws(Exception::class)
    fun addGlobalConstrainsAsList() {
        simple.addGlobalConstraint(sexpr(sym("new"), sym("new2")))
        Assertions.assertEquals(
            fromString(
                "a bb ccc",
                "d ee fff (new new2)"
            ), simple
        )
        other.addGlobalConstraint(sexpr(SList("newA", sexpr("newB", "newC"))))
        Assertions.assertEquals(
            fromString(
                "l o s",
                "ggg (1 2 3 h) i (newA (newB newC))"
            ), other
        )
    }

    @Test
    @Throws(Exception::class)
    fun addHeaderDefinitionsAsArguments() {
        simple.addHeaderDefinition(sym("new"))
        simple.addHeaderDefinition(sym("new2"))
        Assertions.assertEquals(
            fromString(
                "a bb ccc new new2",
                "d ee fff"
            ), simple
        )
        other.addHeaderDefinition(sexpr("newA", sexpr("newB", "newC")))
        Assertions.assertEquals(
            fromString(
                "l o s (newA (newB newC))",
                "ggg (1 2 3 h) i"
            ), other
        )
    }

    @Test
    @Throws(Exception::class)
    fun addHeaderDefinitionsAsList() {
        simple.addHeaderDefinition(sexpr(sym("new"), sym("new2")))
        Assertions.assertEquals(
            fromString(
                "a bb ccc (new new2)",
                "d ee fff"
            ), simple
        )
        other.addHeaderDefinition(sexpr(SList("newA", sexpr("newB", "newC"))))
        Assertions.assertEquals(
            fromString(
                "l o s (newA (newB newC))",
                "ggg (1 2 3 h) i"
            ), other
        )
    }

    @Test
    fun globalConstraints() {
        Assertions.assertEquals(
            listOf(
                sym("d"),
                sym("ee"),
                sym("fff")
            ), simple.globalConstraints
        )
    }

    @Test
    fun variableDefinitions() {
        Assertions.assertEquals(
            listOf(
                sym("a"),
                sym("bb"),
                sym("ccc")
            ), simple.variableDefinitions
        )
    }

    @Test
    @Throws(Exception::class)
    fun testToString() {
        Assertions.assertFalse(simple.toString().isEmpty())
    }

    @Test
    @Throws(Exception::class)
    fun equals() {
        val simpleCompare = fromString(
            "a bb ccc",
            "d ee fff"
        )
        val otherCompare = fromString(
            "l o s",
            "ggg (1 2 3 h) i"
        )
        Assertions.assertEquals(simpleCompare, simple)
        Assertions.assertEquals(otherCompare, other)
        Assertions.assertNotEquals(this, simple)
        Assertions.assertNotEquals(this, other)
        Assertions.assertNotEquals(simple, other)
        Assertions.assertNotEquals("", other)
        Assertions.assertFalse(simple.equals(null))
        Assertions.assertEquals(simple, simple)
    }

    @Test
    @Throws(Exception::class)
    fun testHashCode() {
        val simpleCompare = fromString(
            "a bb ccc",
            "d ee fff"
        )
        val otherCompare = fromString(
            "l o s",
            "ggg (1 2 3 h) i"
        )
        Assertions.assertEquals(simpleCompare.hashCode().toLong(), simple.hashCode().toLong())
        Assertions.assertEquals(otherCompare.hashCode().toLong(), other.hashCode().toLong())
    }


    @Test
    fun testEmptyConstructor() {
        val model = SmtModel()
        Assertions.assertTrue(model.variableDefinitions.isEmpty())
        Assertions.assertTrue(model.globalConstraints.isEmpty())
    }
}