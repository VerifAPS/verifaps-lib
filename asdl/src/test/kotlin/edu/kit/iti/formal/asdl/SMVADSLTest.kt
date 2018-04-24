package edu.kit.iti.formal.asdl

import org.junit.Test
import java.io.File

/**
 * @author Alexander Weigl
 * @version 1 (24.04.18)
 */
class SMVADSLTest {
    @Test
    fun generate() = SMVADSL().generate(File("tmp/smv"))
}