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
package edu.kit.iti.formal.stvs.model.table

import com.google.common.truth.Truth
import com.google.gson.JsonElement
import edu.kit.iti.formal.stvs.model.TestUtils
import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import edu.kit.iti.formal.stvs.model.common.VariableCategory
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows
import kotlin.test.assertFailsWith

/**
 * @author Benjamin Alt
 * @author Philipp
 */
class SpecificationTableTest {
    val elem = JsonTableParser.jsonFromResource("test_table.json", SpecificationTableTest::class.java)
    private var table = JsonTableParser.specificationTableFromJson(elem)

    @Test
    fun testGetCell() {
        assertEquals("B1", table.rows[1].cells["VariableB"])
        assertEquals("D3", table.rows[3].cells["VariableD"])
        assertEquals("A2", table.getColumnByName("VariableA").cells[2])
    }

    @Test // (expected = NoSuchElementException::class)
    fun testGetCellNoSuchColumn() {
        assertFailsWith<NoSuchElementException> {
            table.getColumnByName("VariableE").cells[2]
        }
    }

    @Test // (expected = IndexOutOfBoundsException::class)
    fun testGetCellNoSuchRow() {
        assertFailsWith<IndexOutOfBoundsException> {
            table.getColumnByName("VariableB").cells[4]
        }
    }

    @Test
    fun testGetColumnByName() {
        assertEquals(
            SpecificationColumn(mutableListOf("A0", "A1", "A2", "A3")),
            table.getColumnByName("VariableA"),
        )
    }

    @Test // (expected = NoSuchElementException::class)
    fun testGetColumnNoSuchColumn() {
        assertFailsWith<NoSuchElementException> {
            table.getColumnByName("E")
        }
    }

    @Test
    fun testAddColumn() {
        val widthBefore = table.columnHeaders.size

        val ioVar: SpecIoVariable = SpecIoVariable(VariableCategory.INPUT, "INT", "VariableE")

        val newColumn =
            SpecificationColumn(mutableListOf<String?>("E0", "E1", "E2", "E3"))

        table.addColumn(ioVar, newColumn)

        Assertions.assertTrue(table.columnHeaders.contains(ioVar))
        assertEquals(table.getColumnByName("VariableE"), newColumn)
        assertEquals(table.columnHeaders.size.toLong(), (widthBefore + 1).toLong())
    }

    @Test // (expected = IllegalArgumentException::class)
    @Throws(Throwable::class)
    fun testAddExistingColumn() {
        assertFailsWith<IllegalArgumentException> {
            TestUtils.rethrowThreadUncheckedExceptions {
                val ioVar: SpecIoVariable = SpecIoVariable(VariableCategory.INPUT, "INT", "VariableA")
                val newColumn =
                    SpecificationColumn(mutableListOf<String?>("E0", "E1", "E2", "E3"))
                table.addColumn(ioVar, newColumn)
            }
        }
    }

    @Test // (expected = IllegalArgumentException::class)
    @Throws(Throwable::class)
    fun testAddColumnInvalidSize() {
        assertFailsWith<IllegalArgumentException> {
            TestUtils.rethrowThreadUncheckedExceptions {
                val ioVar: SpecIoVariable = SpecIoVariable(VariableCategory.INPUT, "INT", "VariableA")
                val newColumn =
                    SpecificationColumn(mutableListOf<String?>("E0", "E1", "E2", "E3", "E4"))
                table.addColumn(ioVar, newColumn)
            }
        }
    }

    @Test
    fun testRemoveColumn() {
        val expectedColumn =
            SpecificationColumn(mutableListOf("B0", "B1", "B2", "B3"))

        val removedColumn = table.removeColumnByName("VariableB")

        assertEquals(expectedColumn, removedColumn)
    }

    @Test // (expected = NoSuchElementException::class)
    fun testRemoveColumnActuallyRemoved() {
        val colName = "VariableA"
        table.removeColumnByName(colName)

        assertFailsWith<NoSuchElementException> {
            table.getColumnByName(colName)
        }
    }

    @Test
    fun testGetRow() {
        val row = table.rows[2]
        val expectedCells =
            hashMapOf("VariableA" to "A2", "VariableB" to "B2", "VariableC" to "C2", "VariableD" to "D2")
        Truth.assertThat(row)
            .isEqualTo(SpecificationRow.createUnobservableRow(expectedCells))
    }

    @Test // (expected = IndexOutOfBoundsException::class)
    fun testGetRowNoSuchRow() {
        assertFailsWith<IndexOutOfBoundsException> {
            table.rows[4]
        }
    }

    @Test
    fun testAddRow() {
        val newCells = hashMapOf<String, String>()
        newCells["VariableA"] = "A4"
        newCells["VariableB"] = "B4"
        newCells["VariableC"] = "C4"
        newCells["VariableD"] = "D4"
        val newRow = SpecificationRow.createUnobservableRow(newCells)
        table.rows.add(newRow)
        assertEquals(newRow, table.rows[4])
    }

    @Test
    fun testAddInvalidRow() {
        assertThrows<IllegalArgumentException> {
            TestUtils.rethrowThreadUncheckedExceptions {
                val newCells = mapOf(
                    "VariableA" to "A4",
                    "VariableB" to "B4",
                    "VariableC" to "C4",
                    "VariableX" to "D4",
                )
                val newRow = SpecificationRow.createUnobservableRow(newCells)
                table.rows.add(newRow)
            }
        }
    }

    @Test
    fun testAddInvalidlySizedRow() {
        assertThrows<IllegalArgumentException> {
            TestUtils.rethrowThreadUncheckedExceptions {
                val newCells = mapOf(
                    "VariableA" to "A4",
                    "VariableB" to "B4",
                    "VariableC" to "C4",
                    "VariableD" to "D4",
                    "VariableE" to "E5",
                )
                val newRow = SpecificationRow.createUnobservableRow(newCells)
                table.rows.add(newRow)
            }
        }
    }

    @Test
    fun testAddColumnToEmptyTable() {
        val emptyTable = ConstraintSpecification(FreeVariableList())
        val column = SpecificationColumn(arrayListOf<ConstraintCell?>())
        assertFailsWith<IllegalStateException> {
            emptyTable.addColumn(SpecIoVariable(VariableCategory.INPUT, "INT", "A"), column)
        }
    }

    @Test
    fun testRemoveRow() {
        val expectedCells =
            hashMapOf("VariableA" to "A2", "VariableB" to "B2", "VariableC" to "C2", "VariableD" to "D2")
        val expectedRow = SpecificationRow.createUnobservableRow(expectedCells)

        val removed = table.rows.removeAt(2)
        assertEquals(expectedRow, removed)
    }

    @Test
    fun testGetDuration() {
        val dur0 = table.durations[0]
        val dur2 = table.durations[2]
        assertEquals("2", dur0)
        assertEquals("10", dur2)
    }

    @Test
    fun testEquals() {
        val elem: JsonElement = JsonTableParser.jsonFromResource("test_table.json", SpecificationTableTest::class.java)
        val identical: SpecificationTable<*, *, *> = JsonTableParser.specificationTableFromJson(elem)
        assertEquals(table, identical)
        Assertions.assertNotEquals(table, null)
        identical.name = "SomeOtherName"
        Assertions.assertNotEquals(table, identical)
    }
}