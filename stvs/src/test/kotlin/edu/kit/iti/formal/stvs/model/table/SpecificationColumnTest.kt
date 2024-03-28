package edu.kit.iti.formal.stvs.model.table

import org.junit.Assert
import org.junit.Before
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test

/**
 * Created by bal on 26.02.17.
 */
class SpecificationColumnTest {
    private val column= SpecificationColumn(mutableListOf(1, 2, 3, 4, 5))

    @Test
    fun testEquals() {
        val identical: SpecificationColumn<*> = SpecificationColumn(mutableListOf(1, 2, 3, 4, 5))
        Assertions.assertEquals(identical, column)
        column.comment = "Comment"
        Assertions.assertNotEquals(identical, column)
        identical.comment = "Comment"
        Assertions.assertEquals(identical, column)
        identical.comment = "Different comment"
        Assertions.assertNotEquals(identical, column)
        Assertions.assertNotEquals(null, column)
        Assertions.assertEquals(column, column)
    }

    @Test
    fun testGetSetComment() {
        Assertions.assertEquals("", column.comment)
        column.comment = "Comment"
        Assertions.assertEquals("Comment", column.comment)
        column.comment = "NewComment"
        Assertions.assertEquals("NewComment", column.comment)
    }

    @Test
    fun testToString() {
        column.comment = "Comment"
        Assertions.assertEquals("SpecificationColumn(cells: [1, 2, 3, 4, 5], comment: Comment)", column.toString())
    }
}
