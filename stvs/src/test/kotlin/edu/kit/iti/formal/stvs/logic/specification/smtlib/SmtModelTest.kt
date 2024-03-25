package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.stvs.logic.specification.smtlib.SExpression.Companion.fromSexp
import edu.kit.iti.formal.stvs.logic.specification.smtlib.SExpression.Companion.fromText
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import java.util.*
import java.util.regex.Pattern

/**
 * Created by csicar on 02.03.17.
 */
class SmtModelTest {
    private var simple: SmtModel? = null
    private var other: SmtModel? = null

    private fun fromString(vars: String, constr: String): SmtModel {
        return SmtModel(
            (fromText("($constr)") as SList).list,
            (fromText("($vars)") as SList).list
        )
    }

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
    @Throws(Exception::class)
    fun combine() {
        simple!!.combine(other)
        Assertions.assertEquals(
            fromString(
                "a bb ccc l o s",
                "d ee fff ggg (1 2 3 h) i"
            ), simple
        )
    }

    @Test
    fun isAtom() {
        Assertions.assertFalse(simple!!.isAtom)
    }

    @Test
    @Throws(Exception::class)
    fun toSexpr() {
        Assertions.assertEquals(
            fromText("(a bb ccc ( assert d ) ( assert ee ) ( assert fff) )"),
            fromSexp(simple!!.toSexpr()!!)
        )
    }

    @Test
    @Throws(Exception::class)
    fun headerToText() {
        val result = simple!!.headerToText()
        assertMatches("a bb ccc", result)

        val result2 = other!!.headerToText()
        println(result2)
        assertMatches("l o s", result2)
    }

    @Test
    @Throws(Exception::class)
    fun globalConstraintsToText() {
        val pattern = "( assert d ) ( assert ee ) ( assert fff )"
        assertMatches(pattern, simple!!.globalConstraintsToText())

        assertMatches(
            "( assert ggg ) ( assert ( 1 2 3 h ) ) ( assert i )",
            other!!.globalConstraintsToText()
        )
    }

    @Test
    @Throws(Exception::class)
    fun toText() {
        assertMatches("a bb ccc ( assert d ) ( assert ee ) ( assert fff )", simple!!.toText())
        assertMatches("l o s ( assert ggg ) ( assert ( 1 2 3 h ) ) ( assert i )", other!!.toText())
    }

    @Test
    @Throws(Exception::class)
    fun addGlobalConstrainsAsArguments() {
        simple!!.addGlobalConstrains(SAtom("new"), SAtom("new2"))
        Assertions.assertEquals(
            fromString(
                "a bb ccc",
                "d ee fff new new2"
            ), simple
        )
        other!!.addGlobalConstrains(SList("newA", SList("newB", "newC")))
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
        simple!!.addGlobalConstrains(listOf(SAtom("new"), SAtom("new2")))
        Assertions.assertEquals(
            fromString(
                "a bb ccc",
                "d ee fff new new2"
            ), simple
        )
        other!!.addGlobalConstrains(listOf(SList("newA", SList("newB", "newC"))))
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
        simple!!.addHeaderDefinitions(SAtom("new"), SAtom("new2"))
        Assertions.assertEquals(
            fromString(
                "a bb ccc new new2",
                "d ee fff"
            ), simple
        )
        other!!.addHeaderDefinitions(SList("newA", SList("newB", "newC")))
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
        simple!!.addHeaderDefinitions(listOf(SAtom("new"), SAtom("new2")))
        Assertions.assertEquals(
            fromString(
                "a bb ccc new new2",
                "d ee fff"
            ), simple
        )
        other!!.addHeaderDefinitions(listOf(SList("newA", SList("newB", "newC"))))
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
                SAtom("d"),
                SAtom("ee"),
                SAtom("fff")
            ), simple!!.globalConstraints
        )
    }

    @Test
    fun variableDefinitions() {
        Assertions.assertEquals(
            listOf(
                SAtom("a"),
                SAtom("bb"),
                SAtom("ccc")
            ), simple!!.variableDefinitions
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
        Assertions.assertFalse(simple!!.equals(null))
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