package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.st.ast.EnumerationTypeDeclaration
import edu.kit.iti.formal.automation.st.ast.TypeDeclarations
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import java.util.*

/**
 * @author Philipp Krüger
 * @author Alexander Weigl
 */
class TestEnumParse : DefaultVisitor<Void>() {
    internal var code = "TYPE\n" +
            "  MY_ENUM : (one, two, three);\n" +
            "END_TYPE\n"

    @Test
    fun testEnumMembers() {
        val toplevel = IEC61131Facade.file(CharStreams.fromString(code))
        val decls = toplevel[0] as TypeDeclarations
        val enumdecl = decls[0] as EnumerationTypeDeclaration
        assertEquals(Arrays.asList("one", "two", "three"),
                enumdecl.allowedValues.map { it.text!! })
    }


}
