package edu.kit.iti.formal.automation.analysis

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.st.ast.HasFbBody
import edu.kit.iti.formal.automation.st.ast.HasStBody
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope
import edu.kit.iti.formal.util.CodeWriter

/**
 *
 * @author Alexander Weigl
 * @version 1 (10.07.19)
 */
object TranslateFbdToSt : AstVisitorWithScope<Unit>() {
    override fun defaultVisit(obj: Any) {
        val st = (obj as? HasStBody)
        val body = (obj as? HasFbBody)?.fbBody
        if(st!= null && body!=null) {
            val out = CodeWriter()
            body.asStructuredText(out)
            st.stBody = IEC61131Facade.statements(out.stream.toString())
        }
    }
}