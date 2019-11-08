package edu.kit.iti.formal.automation.datatypes.values

import edu.kit.iti.formal.automation.datatypes.expand
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (08.11.19)
 */
internal class MultiDimArrayValueTest {
    @Test
    fun listIndices(): Unit {
        val d1 = 0..3
        val d2 = 0..3
        val d3 = 0..3
        val ranges = listOf(d1, d2, d3)
        val actual = ranges.expand()
        for (a in actual) {
            println(a.contentToString())
        }
    }

    @Test
    fun testDim3() {
        val d1 = 2..4
        val d2 = -3..-1
        val d3 = 0..2
        val ranges = arrayOf(d1, d2, d3)
        val mdav = NDArray(ranges, 0)

        Assertions.assertEquals(3*3*3, mdav.size)
        Assertions.assertTrue(arrayOf(3,3,3).contentEquals(mdav.spanDim))
        Assertions.assertTrue(arrayOf(9, 3, 1).contentEquals(mdav.facN))

        var cnt = 0
        d1.forEach { i1 ->
            d2.forEach { i2 ->
                d3.forEach { i3 ->
                    val idx = listOf(i1, i2, i3)
                    val pos = mdav.pos(idx)
                    Assertions.assertEquals(pos, cnt)
                    mdav[idx] = cnt++
                    Assertions.assertEquals(cnt - 1, mdav[i1, i2, i3])
                }
            }
        }

        println(mdav.data.contentToString())
        Assertions.assertTrue(Array(27, { it }).contentEquals(mdav.data))
    }
}