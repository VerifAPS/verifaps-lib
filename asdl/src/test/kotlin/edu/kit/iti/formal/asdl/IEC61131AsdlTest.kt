package edu.kit.iti.formal.asdl

import org.junit.Test

import org.junit.Assert.*
import java.io.File

/**
 * @author Alexander Weigl
 * @version 1 (24.04.18)
 */
class IEC61131AsdlTest {
    @Test
    fun generate() = IEC61131Asdl().generate(File("tmp/iec"))
}