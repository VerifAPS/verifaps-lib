package edu.kit.iti.formal.stvs.model.table


import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

/**
 * Created by bal on 25.02.17.
 */
class HybridCellTest {
    private var hybridCell: HybridCell<ConstraintCell>? = null

    @BeforeEach
    @Throws(Exception::class)
    fun setUp() {
        hybridCell = HybridCell(ConstraintCell("3"))
    }

    @Test
    @Throws(Exception::class)
    fun setFromString() {
        Assertions.assertNotEquals("asdf", hybridCell!!.asString)
        hybridCell!!.setFromString("asdf")
        Assertions.assertEquals("asdf", hybridCell!!.asString)
    }

    @Test
    fun testSetComment() {
        Assertions.assertNotEquals("asdf", hybridCell!!.asString)
        hybridCell!!.comment = "I am a comment!"
        Assertions.assertEquals("I am a comment!", hybridCell!!.comment)
    }
}