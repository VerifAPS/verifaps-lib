package edu.kit.iti.formal.stvs.model.table

import javafx.beans.Observable
import javafx.beans.property.SimpleStringProperty
import javafx.beans.property.StringProperty
import javafx.collections.FXCollections
import javafx.util.Callback
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

/**
 * @author Benjamin Alt
 * @author Philipp
 */
class SpecificationRowTest {
    private val toBeChanged: StringProperty = SimpleStringProperty("")
    private var specRow: SpecificationRow<StringProperty> = SpecificationRow(HashMap(), identityExtractor())
    private var listenerCalls = 0

    @BeforeEach
    fun setUp() {
        specRow = SpecificationRow(HashMap(), identityExtractor())
        specRow.cells["abc"] = toBeChanged
        listenerCalls = 0
    }

    @Test
    fun testInvalidationListener() {
        specRow.addListener { _: Observable? -> listenerCalls++ }

        Assertions.assertEquals(0, listenerCalls.toLong(), "listener calls before change")
        toBeChanged.set("XYZ")
        Assertions.assertEquals(1, listenerCalls.toLong(), "listener calls after change")
    }

    @Test
    fun testNestedRows() {
        val rows =
            FXCollections.observableList(
                listOf(specRow),
                identityExtractor()
            )
        rows.addListener { _: Observable? -> listenerCalls++ }

        Assertions.assertEquals(0, listenerCalls.toLong(), "listener calls before change")
        toBeChanged.set("XXX")
        Assertions.assertEquals(1, listenerCalls.toLong(), "listener calls after change")

        val toBeAddedChangedRemoved: StringProperty = SimpleStringProperty("")

        rows[0]!!.cells["toBeAddedChangedRemoved"] = toBeAddedChangedRemoved
        Assertions.assertEquals(2, listenerCalls.toLong(), "listener calls after adding")

        toBeAddedChangedRemoved.set("ASDF")
        Assertions.assertEquals(3, listenerCalls.toLong(), "listener calls after changing added")

        rows[0]!!.cells.remove("toBeAddedChangedRemoved")
        Assertions.assertEquals(4, listenerCalls.toLong(), "listener calls after removing")

        toBeAddedChangedRemoved.set("SHOULD NOT FIRE EVENT")
        Assertions.assertEquals(4, listenerCalls.toLong(), "listener calls after changing cell that was removed")
    }

    @Test
    fun testUnobservableRow() {
        val cells = hashMapOf<String, StringProperty>()
        cells["abc"] = toBeChanged
        val unobservable: SpecificationRow<*> = SpecificationRow.createUnobservableRow(cells)
        unobservable.addListener { _: Observable? -> listenerCalls++ }
        Assertions.assertEquals(0, listenerCalls.toLong(), "listener calls before change")
        toBeChanged.set("XYZ")
        Assertions.assertEquals(0, listenerCalls.toLong(), "listener calls after change")
        cells["def"] = SimpleStringProperty("test")
        Assertions.assertEquals(0, listenerCalls.toLong(), "listener calls after add")
    }

    @Test
    fun testEquals() {
        val otherRow = SpecificationRow(HashMap(), identityExtractor())
        otherRow.cells["abc"] = toBeChanged
        Assertions.assertEquals(otherRow, specRow)
        Assertions.assertEquals(specRow, specRow)
        otherRow.cells["abc"] = SimpleStringProperty("something else")
        Assertions.assertNotEquals(otherRow, specRow)
        Assertions.assertNotEquals(specRow, null)
    }

    @Test
    fun testHashCode() {
        val otherRow = SpecificationRow(HashMap(), identityExtractor())
        otherRow.cells["abc"] = toBeChanged
        Assertions.assertEquals(otherRow.hashCode().toLong(), specRow.hashCode().toLong())
        otherRow.cells["abd"] = SimpleStringProperty("something else")
        Assertions.assertNotEquals(otherRow.hashCode().toLong(), specRow.hashCode().toLong())
    }

    companion object {
        private fun <E : Observable> identityExtractor(): Callback<E, Array<Observable>> {
            return Callback { arrayOf(it) }
        }
    }
}
