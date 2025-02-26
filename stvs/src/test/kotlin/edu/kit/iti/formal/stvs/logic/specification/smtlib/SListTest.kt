package edu.kit.iti.formal.stvs.logic.specification.smtlib
/*
import edu.kit.iti.formal.smt.SExprFacade.sexpr
import edu.kit.iti.formal.smt.SList
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.util.*

/**
 * Created by csicar on 28.02.17.
 */
class SListTest {
    val simple = SList("testValue")
    val multivalue = sexpr("val1", "val2", "val3")
    val nested = sexpr("val1", sexpr("nested1.1", "nested1.2"), sexpr("nested2.1"))

    @Test
    fun isAtom() {
        Assertions.assertEquals(false, simple.isAtom)
        Assertions.assertEquals(false, multivalue.isAtom)
        Assertions.assertEquals(false, nested.isAtom)
    }

    @Test
    fun testToString() {
        Assertions.assertEquals(" ( testValue ) ", simple.toString())
        Assertions.assertEquals(" ( val1 val2 val3 ) ", multivalue.toString())
        Assertions.assertEquals(" ( val1  ( nested1.1 nested1.2 )   ( nested2.1 )  ) ", nested.toString())
    }

    @Test
    fun addAllStringArguments() {
        val newElements = mutableListOf("add1", "add2", "add3")

        simple.addAll("add1", "add2", "add3")
        Assertions.assertEquals(SList("testValue", "add1", "add2", "add3"), simple)
        multivalue.addAll("add1", "add2", "add3")
        Assertions.assertEquals(SList("val1", "val2", "val3", "add1", "add2", "add3"), multivalue)
        nested.addAll("add1", "add2", "add3")
        Assertions.assertEquals(
            SList(
                "val1",
                SList("nested1.1", "nested1.2"),
                SList("nested2.1"),
                sym("add1"),
                sym("add2"),
                sym("add3")
            ), nested
        )
    }

    @Test
    @Throws(Exception::class)
    fun addAllArgumentExpressions() {
        val newElements: List<String> = mutableListOf("add1", "add2", "add3")

        simple.addAll(
            sym("add1"),
            sym("add2"),
            sym("add3")
        )
        Assertions.assertEquals(SList("testValue", "add1", "add2", "add3"), simple)
        simple.addAll(
            sym("add4"),
            sym("add5")
        )
        Assertions.assertEquals(SList("testValue", "add1", "add2", "add3", "add4", "add5"), simple)


        multivalue.addAll(
            sym("add1"),
            sym("add2"),
            sym("add3")
        )
        Assertions.assertEquals(SList("val1", "val2", "val3", "add1", "add2", "add3"), multivalue)

        nested.addAll(
            sym("add1"),
            sym("add2"),
            sym("add3")
        )
        Assertions.assertEquals(
            SList(
                "val1",
                SList("nested1.1", "nested1.2"),
                SList("nested2.1"),
                sym("add1"),
                sym("add2"),
                sym("add3")
            ), nested
        )

        val inner = SList("inner1", "inner2")
        simple.addAll(inner)
        inner.addAll(sym("inner3"))
        Assertions.assertEquals(
            SList(
                "testValue", sym("add1"), sym("add2"), sym("add3"),
                sym("add4"), sym("add5"), SList("inner1", "inner2", "inner3")
            ), simple
        )
    }

    @Test
    @Throws(Exception::class)
    fun addAllListOfExpressions() {
        val newElements: List<String> = mutableListOf("add1", "add2", "add3")

        simple.addAll(
            Arrays.asList(
                sym("add1"),
                sym("add2"),
                sym("add3")
            )
        )
        Assertions.assertEquals(SList("testValue", "add1", "add2", "add3"), simple)
        simple.addAll(
            Arrays.asList(
                sym("add4"),
                sym("add5")
            )
        )
        Assertions.assertEquals(SList("testValue", "add1", "add2", "add3", "add4", "add5"), simple)

        multivalue.addAll(
            Arrays.asList(
                sym("add1"),
                sym("add2"),
                sym("add3")
            )
        )
        Assertions.assertEquals(SList("val1", "val2", "val3", "add1", "add2", "add3"), multivalue)

        nested.addAll(
            Arrays.asList(
                sym("add1"),
                sym("add2"),
                sym("add3")
            )
        )
        Assertions.assertEquals(
            SList(
                "val1",
                SList("nested1.1", "nested1.2"),
                SList("nested2.1"),
                sym("add1"),
                sym("add2"),
                sym("add3")
            ), nested
        )

        val inner = SList("inner1", "inner2")
        simple.addAll(inner)
        inner.addAll(Arrays.asList(sym("inner3")))
        Assertions.assertEquals(
            SList(
                "testValue", sym("add1"), sym("add2"), sym("add3"),
                sym("add4"), sym("add5"), SList("inner1", "inner2", "inner3")
            ), simple
        )
    }

    @Test
    @Throws(Exception::class)
    fun addListElements() {
        simple.addListElements(
            mutableListOf<String?>(
                "add1", "add2", "add3"
            )
        )
        Assertions.assertEquals(SList("testValue", "add1", "add2", "add3"), simple)

        multivalue.addListElements(
            mutableListOf<String?>(
                "add1", "add2", "add3"
            )
        )
        Assertions.assertEquals(SList("val1", "val2", "val3", "add1", "add2", "add3"), multivalue)

        nested.addListElements(
            mutableListOf<String?>(
                "add1", "add2", "add3"
            )
        )
        Assertions.assertEquals(
            SList(
                "val1",
                SList("nested1.1", "nested1.2"),
                SList("nested2.1"),
                sym("add1"),
                sym("add2"),
                sym("add3")
            ), nested
        )
    }

    @get:Throws(Exception::class)
    @get:Test
    val list: Unit
        get() {
            Assertions.assertEquals(
                Arrays.asList(
                    sym("testValue")
                ), simple.list
            )
            Assertions.assertEquals(
                Arrays.asList(
                    sym("val1"),
                    sym("val2"),
                    sym("val3")
                ), multivalue.list
            )
            Assertions.assertEquals(
                Arrays.asList(
                    sym("val1"),
                    SList("nested1.1", "nested1.2"),
                    SList("nested2.1")
                ), nested.list
            )
        }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        Assertions.assertEquals(SList("testValue"), simple)
        Assertions.assertEquals(SList("testValue") as SExpression, simple)
        Assertions.assertEquals(SList("val1", "val2", "val3"), multivalue)
        Assertions.assertEquals(
            SList(
                Arrays.asList(
                    sym("val1"),
                    SList("nested1.1", "nested1.2"),
                    SList("nested2.1")
                )
            ), nested
        )
        Assertions.assertEquals(simple, simple)
        Assertions.assertEquals(multivalue, multivalue)
        Assertions.assertEquals(nested, nested)
        Assertions.assertNotEquals(SList("testValue", "val2"), simple)
        Assertions.assertNotEquals(SList(), simple)
        Assertions.assertNotEquals(SList("val1", "val2", "val3", "val4", "val4"), multivalue)
        Assertions.assertNotEquals(SList(), multivalue)
        Assertions.assertNotEquals(this, simple)
        Assertions.assertNotEquals(this, multivalue)
        Assertions.assertNotEquals(this, nested)
        Assertions.assertFalse(nested.equals(null))
    }

    @Test
    @Throws(Exception::class)
    fun testHashCode() {
        Assertions.assertEquals(SList("testValue").hashCode().toLong(), simple.hashCode().toLong())
        Assertions.assertEquals((SList("testValue") as SExpression).hashCode().toLong(), simple.hashCode().toLong())
        Assertions.assertEquals(SList("val1", "val2", "val3").hashCode().toLong(), multivalue.hashCode().toLong())
        Assertions.assertEquals(
            SList(
                Arrays.asList(
                    sym("val1"),
                    SList("nested1.1", "nested1.2"),
                    SList("nested2.1")
                )
            ).hashCode().toLong(), nested.hashCode().toLong()
        )
    }

    @Test
    @Throws(Exception::class)
    fun toSexpr() {
        val sexp = SexpFactory.newNonAtomicSexp()
        sexp.add(SexpFactory.newAtomicSexp("testValue"))
        Assertions.assertEquals(sexp, simple.toSexpr())
    }


    @Test
    fun testSexprConstructor() {
        val sexp = SexpFactory.newNonAtomicSexp()
        sexp.add(SexpFactory.newAtomicSexp("testValue"))
        Assertions.assertEquals(SList(sexp), simple)
    }

    @Test
    @Throws(Exception::class)
    fun toStringTest() {
        Assertions.assertNotEquals("", simple.toString())
    }
}*/