package edu.kit.iti.formal.automation

import edu.kit.iti.formal.automation.rvt.*
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.smv.ast.SMVModule

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.03.19)
 */
object LinReReve {
    @JvmStatic
    fun main(args: Array<String>) {
        RvtAps.main(arrayOf(
                "-v",
                "--old", "aps-rvt/examples/LinRe/lr.old.st",
                "--new", "aps-rvt/examples/LinRe/lr.new.st",
                "--output", "aps-rvt/examples/LinRe/out"
        ))
    }
}