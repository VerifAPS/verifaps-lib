package edu.kit.iti.formal.stvs.model.table

import com.google.gson.JsonElement
import edu.kit.iti.formal.stvs.model.TestUtils
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import org.junit.Assert
import org.junit.Before
import org.junit.jupiter.api.Test

/**
 * @author Benjamin Alt
 * @author Philipp
 */
class SpecificationTableTest {
    private var table: SpecificationTable<SpecIoVariable, String?, String?>? = null

    @Before
    fun setUp() {
        val elem = JsonTableParser.jsonFromResource("test_table.json", SpecificationTableTest::class.java)
        table = JsonTableParser.specificationTableFromJson(elem)
    }

    @Test
    fun testGetCell() {
        Assert.assertEquals("B1", table!!.rows[1].cells["VariableB"])
        Assert.assertEquals("D3", table!!.rows[3].cells["VariableD"])
        Assert.assertEquals("A2", table!!.getColumnByName("VariableA").cells[2])
    }

    @Test(expected = NoSuchElementException::class)
    fun testGetCellNoSuchColumn() {
        table!!.getColumnByName("VariableE").cells[2]
    }

    @Test(expected = IndexOutOfBoundsException::class)
    fun testGetCellNoSuchRow() {
        table!!.getColumnByName("VariableB").cells[4]
    }

    @Test
    fun testGetColumnByName() {
        Assert.assertEquals(
            SpecificationColumn(mutableListOf("A0", "A1", "A2", "A3")),
            table!!.getColumnByName("VariableA")
        )
    }

    @Test(expected = NoSuchElementException::class)
    fun testGetColumnNoSuchColumn() {
        table!!.getColumnByName("E")
    }

    @Test
    fun testAddColumn() {
        val widthBefore = table!!.columnHeaders.size

        val ioVar: SpecIoVariable = SpecIoVariable(VariableCategory.INPUT, "INT", "VariableE")

        val newColumn =
            SpecificationColumn(mutableListOf<String?>("E0", "E1", "E2", "E3"))

        table!!.addColumn(ioVar, newColumn)

        Assert.assertTrue(table!!.columnHeaders.contains(ioVar))
        Assert.assertEquals(table!!.getColumnByName("VariableE"), newColumn)
        Assert.assertEquals(table!!.columnHeaders.size.toLong(), (widthBefore + 1).toLong())
    }

    @Test(expected = IllegalArgumentException::class)
    @Throws(Throwable::class)
    fun testAddExistingColumn() {
        TestUtils.rethrowThreadUncheckedExceptions {
            val ioVar: SpecIoVariable = SpecIoVariable(VariableCategory.INPUT, "INT", "VariableA")
            val newColumn =
                SpecificationColumn(mutableListOf<String?>("E0", "E1", "E2", "E3"))
            table!!.addColumn(ioVar, newColumn)
        }
    }

    @Test(expected = IllegalArgumentException::class)
    @Throws(Throwable::class)
    fun testAddColumnInvalidSize() {
        TestUtils.rethrowThreadUncheckedExceptions {
            val ioVar: SpecIoVariable = SpecIoVariable(VariableCategory.INPUT, "INT", "VariableA")
            val newColumn =
                SpecificationColumn(mutableListOf<String?>("E0", "E1", "E2", "E3", "E4"))
            table!!.addColumn(ioVar, newColumn)
        }
    }

    @Test
    fun testRemoveColumn() {
        val expectedColumn =
            SpecificationColumn(mutableListOf("B0", "B1", "B2", "B3"))

        val removedColumn = table!!.removeColumnByName("VariableB")

        Assert.assertEquals(expectedColumn, removedColumn)
    }

    @Test(expected = NoSuchElementException::class)
    fun testRemoveColumnActuallyRemoved() {
        val colName = "VariableA"
        table!!.removeColumnByName(colName)
        table!!.getColumnByName(colName)
    }

    @Test
    fun testGetRow() {
        val row = table!!.rows[2]
        val expectedCells = HashMap<String?, String>()
        expectedCells["VariableA"] = "A2"
        expectedCells["VariableB"] = "B2"
        expectedCells["VariableC"] = "C2"
        expectedCells["VariableD"] = "D2"
        assertEquals(SpecificationRow.createUnobservableRow(expectedCells), row)
    }

    @Test(expected = IndexOutOfBoundsException::class)
    fun testGetRowNoSuchRow() {
        table!!.rows[4]
    }

    @Test
    fun testAddRow() {
        val newCells = HashMap<String?, String>()
        newCells["VariableA"] = "A4"
        newCells["VariableB"] = "B4"
        newCells["VariableC"] = "C4"
        newCells["VariableD"] = "D4"
        val newRow: SpecificationRow<String?> = SpecificationRow.createUnobservableRow(newCells)

        table!!.rows.add(newRow)

        Assert.assertEquals(newRow, table!!.rows[4])
    }

    @Test(expected = IllegalArgumentException::class)
    @Throws(Throwable::class)
    fun testAddInvalidRow() {
        TestUtils.rethrowThreadUncheckedExceptions {
            val newCells = HashMap<String?, String>()
            newCells["VariableA"] = "A4"
            newCells["VariableB"] = "B4"
            newCells["VariableC"] = "C4"
            newCells["VariableX"] = "D4"
            val newRow: SpecificationRow<String?> = SpecificationRow.createUnobservableRow(newCells)
            table!!.rows.add(newRow)
        }
    }

    @Test(expected = IllegalArgumentException::class)
    @Throws(Throwable::class)
    fun testAddInvalidlySizedRow() {
        TestUtils.rethrowThreadUncheckedExceptions {
            val newCells = HashMap<String?, String>()
            newCells["VariableA"] = "A4"
            newCells["VariableB"] = "B4"
            newCells["VariableC"] = "C4"
            newCells["VariableD"] = "D4"
            newCells["VariableE"] = "E5"
            val newRow: SpecificationRow<String?> = SpecificationRow.createUnobservableRow(newCells)
            table!!.rows.add(newRow)
        }
    }

    @Test(expected = IllegalStateException::class)
    fun testAddColumnToEmptyTable() {
        val emptyTable: SpecificationTable<*, *, *> = ConstraintSpecification(FreeVariableList())
        val column: SpecificationColumn<*> = SpecificationColumn(ArrayList<Any?>())
        emptyTable.addColumn(SpecIoVariable(VariableCategory.INPUT, "INT", "A"), column)
    }

    @Test
    fun testRemoveRow() {
        val expectedCells = HashMap<String?, String>()
        expectedCells["VariableA"] = "A2"
        expectedCells["VariableB"] = "B2"
        expectedCells["VariableC"] = "C2"
        expectedCells["VariableD"] = "D2"
        val expectedRow = SpecificationRow.createUnobservableRow(expectedCells)

        val removed = table!!.rows.removeAt(2)
        Assert.assertEquals(expectedRow, removed)
    }

    @Test
    fun testGetDuration() {
        val dur0 = table!!.durations[0]
        val dur2 = table!!.durations[2]
        Assert.assertEquals("2", dur0)
        Assert.assertEquals("10", dur2)
    }

    @Test
    fun testEquals() {
        val elem: JsonElement? = JsonTableParser.jsonFromResource("test_table.json", SpecificationTableTest::class.java)
        val identical: SpecificationTable<*, *, *>? = JsonTableParser.specificationTableFromJson(elem)
        Assert.assertEquals(table, identical)
        Assert.assertNotEquals(table, null)
        identical!!.name = "SomeOtherName"
        Assert.assertNotEquals(table, identical)
    }
}
