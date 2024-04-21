package edu.kit.iti.formal.stvs.model.common


import org.junit.Assert
import org.junit.jupiter.api.Test

/**
 * Created by Lukas on 22.02.2017.
 *
 * @author Lukas
 */
class CodeIoVariableTest {
    private val var1 = CodeIoVariable(VariableCategory.INPUT, "BOOL", "var")
    private val var2 = CodeIoVariable(VariableCategory.INPUT, "BOOL", "var")
    private val `object` = Any()

    @Test
    @Throws(Exception::class)
    fun equalsCodeIoVariable() {
        Assert.assertTrue(var1 == var2)
        Assert.assertNotEquals(CodeIoVariable(VariableCategory.INPUT, "INT", "var"), var2)
    }

    @Test
    fun testHashCode() {
        Assert.assertEquals(var1.hashCode().toLong(), var2.hashCode().toLong())
        Assert.assertNotEquals(
            CodeIoVariable(VariableCategory.INPUT, "INT", "var").hashCode().toLong(),
            var2.hashCode().toLong()
        )
    }

    @Test
    @Throws(Exception::class)
    fun equalsObject() {
        Assert.assertTrue(var1 != `object`)
    }
}