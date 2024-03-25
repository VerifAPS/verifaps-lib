package edu.kit.iti.formal.stvs.model.table

import org.junit.Assert
import org.junit.Before
import org.junit.jupiter.api.Test

/**
 * Created by bal on 26.02.17.
 */
class SpecificationColumnTest {
    private var column: SpecificationColumn<Int>? = null

    @Before
    fun setUp() {
        column = SpecificationColumn(mutableListOf(1, 2, 3, 4, 5))
    }

    @Test
    @Throws(Exception::class)
    fun testEquals() {
        val identical: SpecificationColumn<*> = SpecificationColumn(mutableListOf(1, 2, 3, 4, 5))
        Assert.assertEquals(identical, column)
        column!!.comment = "Comment"
        Assert.assertNotEquals(identical, column)
        identical.comment = "Comment"
        Assert.assertEquals(identical, column)
        identical.comment = "Different comment"
        Assert.assertNotEquals(identical, column)
        Assert.assertNotEquals(null, column)
        Assert.assertEquals(column, column)
    }

    @Test
    fun testGetSetComment() {
        Assert.assertEquals("", column!!.comment)
        column!!.comment = "Comment"
        Assert.assertEquals("Comment", column!!.comment)
        column!!.comment = "NewComment"
        Assert.assertEquals("NewComment", column!!.comment)
    }

    @Test
    @Throws(Exception::class)
    fun testToString() {
        column!!.comment = "Comment"
        Assert.assertEquals(
            "SpecificationColumn(cells: [1, 2, 3, 4, 5], comment: Comment)",
            column.toString()
        )
    }
}
