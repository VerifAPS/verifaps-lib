package edu.kit.iti.formal.util

import org.junit.Test

import org.junit.Assert.*
import org.junit.jupiter.api.DynamicTest
import org.junit.jupiter.api.TestFactory

/**
 * @author Alexander Weigl
 * @version 1 (03.02.19)
 */
class DLevenshteinTest {
    @TestFactory
    fun dlevenshtein() : Collection<DynamicTest> =
        listOf(dlevenshteinTest("","",0),
                dlevenshteinTest("ac","ac",0),
                dlevenshteinTest("abc","aXc",1),
                dlevenshteinTest("abc","bac",1),
                dlevenshteinTest("abc","",3),
                dlevenshteinTest("abc","cba",2)
                )

    private fun dlevenshteinTest(source: String, target: String, expCost: Int) =
        DynamicTest.dynamicTest("$source/$target/$expCost", {doTest(source,target,expCost)})

    private fun doTest(source: String, target: String, expCost: Int) {
        assertEquals(expCost, edu.kit.iti.formal.util.dlevenshtein(source, target))
    }
}